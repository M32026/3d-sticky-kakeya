/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFibreSupplyProducer
public import Kakeya.DimensionThree.MainLemma2.SetupAbsorption

/-!
# Closing the producer's rows: fullness, tower data, the window body, and one `∀ᶠ` tail

`NEXT`'s five items on `SpineFibreSupplyProducer.lean`.  Three are closed, two are reduced to the
source's own displayed hypotheses, and each reduction is **measured**, not asserted.

## 1. The rows are now read on the refined tower only

`refinedSupplyAt_of_tightRows` takes `FibreWindowRows` **inside** the `∃ S' hS' hhom` binder, so
the producer no longer demands the rows of every tower with tubes in the unit ball — only of
`refinedHierarchy 𝒱 hS' hhom rfl`, which is where the source states them.  Its conclusion is the
same `RefinedSupplyAt`, so `refinedFloorSupplyAt_of_refinedSupplyAt` applies unchanged, and
`refinedFloorSupplyAt_of_tightRows` is the composite that `RefinedFloorPayload` quantifies.

## 2. `FillAt`: produced from volumes, and the honest measurement of what that buys

`densityIn_nodesUnder_self` (existing) makes the right-hand side of `FillAt` the **volume fraction**
`(Σ_{𝕋_c[T_k]}|T_c|) / |T_k|`, and `maxDensity_le_card` bounds the left by `κ · #𝕋_c[T_k]`.  So

> `fillAt_of_volume` — a per-cell volume floor `v₀` with `κ·|T_k| ≤ v₀` gives `FillAt 𝒰 κ k c j`,

with no geometry at all, and `fillAt_of_gridScale` reads it on the grid through the two dimensional
tube-volume constants: `Tube.le_volume` (`c₃ρ_c²` from below) and `Tube.volume_le` (`C₃ρ_k²` from
above).  **This is a real producer of the row and it is now.**

**What it does not buy, measured.**  The κ it delivers satisfies `κ·C₃ρ_k² ≤ c₃ρ_c²`, i.e.
`κ ≲ (ρ_c/ρ_k)²`; `fillAt_of_gridScale_kappa_cap` compiles the degenerate case `k = c`, where the
hypothesis already forces `κ·C₃ ≤ c₃`, so the volume route **never** reaches `κ = 1`.  At the site
`hfill` is used (`k = a`, `c = m'`) this gives `κ ≈ (ρ_{m'}/ρ_a)²`, while `hclose` carries `κ` on
its *larger* side and needs `(ρ_a/ρ_{m'})^{3η/4}·κ` to dominate a δ-free constant — and
`3η/4 ≪ 2`, so the product tends to `0`.  The two rows are therefore in the exact tension the
existing `SpineFloorShapeHwinfloor.lean` docstring records (`hclose` wants `κ` large, `hfill` caps it
at `1`), and the volume route sits at the wrong end of it.

**Why the joint bin does not close it either.**  `exists_shadedRefinement_of_joint_bin`'s conjuncts
band *quantities across cells* — two-level densities, two-level counts, descendant counts, fibre
shaded masses, each pairwise within a factor two at a fixed level.  `FillAt` is not of that form:
it compares, **inside one cell**, the maximizing test body with the node's own tube.  No band
across cells implies it, and `IsShadedRefinementOf.retention` is a statement about the retained
*mass* `Σ|Z|`, not about which body attains `Δ_max`.  Source l.4675-4677 says the four lower-
fullness estimates *"refer to the same mass-coupled refinements, so the corresponding multiplicity
factors may be multiplied"* — that licenses **multiplying the losses of one refinement**, which is
what `IsShadedRefinementOf` already carries; it does not derive fullness.  So a usable `κ` remains
the source's own fullness clause, l.4030-4031 (*"with fullness at least `δ^{3η_f}`"*), which is a
hypothesis of the source's lemma too.

## 3. `hGood` and `hcrude`: reduced to cardinality data, and what the block does not give

* `hcrude_of_cardEstimate` reduces `hcrude` to the source's displayed estimate
  `#𝕋_l⟨S⟩ ≤ D(ρ_k/ρ_l)^4` (l.2679-2681), **on thread cells**, which is exactly how the source
  states it.  The one-trial lemma's global row `#𝕋_k ≤ (32/ρ_k)^6` (l.5825) is a bound on the whole
  level and does **not** give the relative, per-cell one: it has no `(ρ_k/ρ_l)` on the right at all,
  and dividing a global count by nothing yields no per-cell bound.
* `hGood_of_card` reduces `hGood` to `#s ≤ (ρ_0/ρ_L)^{η_0} = δ^{-η_0}`, since
  `Δ_max ≤ #` and the thread cell is an image of a subfamily of `s`.  **The block's card row does
  not meet it:** `SiteWitness` carries `(#s : ℝ) ≤ δ^{-4}`, and `δ^{-4} ≤ δ^{-η_0}` would need
  `η_0 ≥ 4`, whereas `η_0 = spineNu β ϖ ε₁ gain dens` is the *smallest* rung.  So `hGood` is the
  source's assumed top-cell estimate (l.2683-2684) and is not derivable from a counting row —
  which is precisely why the source assumes it.

Both are now in their reduced, source-shaped form, so a caller supplies a **cardinality**
statement rather than a density statement.

## 4. `le_window_maxDensity`: the volume floor is supplied; the body is not

`window_field_of_body` fixes `v₀ := c₃ρ²` from `Tube.le_volume` at the window radius — the
rescaled fine tubes are honest `ρ`-tubes — so of `le_window_maxDensity_of_card`'s four inputs only
the containing body `K` and the one numerical inequality remain, and the **count is not fed
circularly**: `SpineFibreSupplyProducer.lean` measured that `FloorHypothesisAt`'s third conjunct is
an *output* of the window, so it is not used here.  The numerical row is stated with `v₀` already
substituted, i.e. as
`(ρ_a/ρ)^{η_{m+1}}·|K| ≤ C* · #(nodesUnder b a j) · c₃ρ²`.

## 5. One `∀ᶠ` tail

`FibreThresholds` bundles the five δ-rows (`0 < L`, `4δ^{1/L} ≤ 1`, the chain constant, `Cu ≤
δ^{-2η'}`, and `C·totalLoss ≤ δ^{-ν/20}`), and `eventually_fibreThresholds` produces the bundle on
`𝓝[>] 0` — the `Cu ≤ δ^{-2η'}` row outright, from the existing
`Kakeya.VeryNotSticky.eventually_ennreal_le_rpow_neg`, and the grid row and the two `totalLoss`
rows from the caller's own eventualities (they are statements about `totalLoss`, whose absorbers
live with it).  The producer therefore has a **single** filter hypothesis.

## Family / shading / level pair

| declaration | family / shading | level pair |
|---|---|---|
| `fillAt_of_volume`, `fillAt_of_gridScale` | the tower; no shading | `(k,c)` at node `j` |
| `window_field_of_body` | the tower; no shading | `(a,b)` at radius `ρ` |
| `hGood_of_card` | the tower; no shading | `(0,L)` |
| `hcrude_of_cardEstimate` | the tower; no shading | every `(p,c)` |
| `FibreThresholds`, `eventually_fibreThresholds` | none — scalars | none |
| `refinedSupplyAt_of_tightRows` + corollary | `v` refined to `S'`; shading `Z` | `(a,b,m)` |

## A1-a

No `GridUniformCore`; no `(F)`-branch interface statement is defined or altered.  `FillAt`,
`FloorHypothesisAt`, `IsShadedRefinementOf` and `RefinedFloorSupplyAt` are all used as printed.
-/

@[expose] public section

open scoped NNReal ENNReal
open MeasureTheory Tube

namespace Kakeya.ML2Core

section FillFromVolume

universe u

variable {ι : Type u} {δ Cu : NNReal} {s : Finset ι}
  {T : ι → Tube δ (EuclideanSpace ℝ (Fin 3))}

open scoped Classical in
/-- **`FillAt` from volumes alone.** -/
theorem fillAt_of_volume (𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu)
    {κ : ℝ} {k c : ℕ} {j : ι} {v₀ : ENNReal}
    (hv₀ : ∀ j' ∈ 𝒰.nodesUnder c k j, v₀ ≤ volume (𝒰.cover.tube c j').carrier)
    (hk0 : volume (𝒰.cover.tube k j).carrier ≠ 0)
    (hktop : volume (𝒰.cover.tube k j).carrier ≠ ⊤)
    (hκ : ENNReal.ofReal κ * volume (𝒰.cover.tube k j).carrier ≤ v₀) :
    FillAt 𝒰 κ k c j := by
  classical
  unfold FillAt
  rw [densityIn_nodesUnder_self 𝒰 c k j, ENNReal.le_div_iff_mul_le (Or.inl hk0) (Or.inl hktop)]
  calc ENNReal.ofReal κ * Kakeya.maxDensity (𝒰.nodesUnder c k j)
          (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)
        * volume (𝒰.cover.tube k j).carrier
      ≤ ENNReal.ofReal κ * ((𝒰.nodesUnder c k j).card : ENNReal)
          * volume (𝒰.cover.tube k j).carrier :=
        mul_le_mul' (mul_le_mul' le_rfl (Kakeya.maxDensity_le_card _ _)) le_rfl
    _ = ((𝒰.nodesUnder c k j).card : ENNReal)
          * (ENNReal.ofReal κ * volume (𝒰.cover.tube k j).carrier) := by ring
    _ ≤ ((𝒰.nodesUnder c k j).card : ENNReal) * v₀ := mul_le_mul' le_rfl hκ
    _ = ∑ _j' ∈ 𝒰.nodesUnder c k j, v₀ := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ j' ∈ 𝒰.nodesUnder c k j, volume (𝒰.cover.tube c j').carrier :=
        Finset.sum_le_sum hv₀

open scoped Classical in
/-- **`FillAt` on the grid, with the two dimensional tube-volume constants exposed.** -/
theorem fillAt_of_gridScale (hδ1 : δ ≤ 1)
    (𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu) {κ : ℝ} {k c : ℕ} {j : ι}
    (hκ : ENNReal.ofReal κ
        * ((Tube.volume_le.C 3 : NNReal) : ENNReal)
        * ((Tube.gridScale δ (Tube.ssfGridLen δ) k : NNReal) : ENNReal) ^ (2 : ℕ)
      ≤ ((Tube.le_volume.c 3 : NNReal) : ENNReal)
        * ((Tube.gridScale δ (Tube.ssfGridLen δ) c : NNReal) : ENNReal) ^ (2 : ℕ))
    (hk0 : volume (𝒰.cover.tube k j).carrier ≠ 0)
    (hktop : volume (𝒰.cover.tube k j).carrier ≠ ⊤) :
    FillAt 𝒰 κ k c j := by
  classical
  have hrank : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  refine fillAt_of_volume 𝒰 (v₀ := ((Tube.le_volume.c 3 : NNReal) : ENNReal)
      * ((Tube.gridScale δ (Tube.ssfGridLen δ) c : NNReal) : ENNReal) ^ (2 : ℕ)) ?_ hk0 hktop ?_
  · intro j' _
    have := Tube.le_volume (E := EuclideanSpace ℝ (Fin 3)) (𝒰.cover.tube c j')
    rw [hrank] at this
    simpa using this
  · have hvol := Tube.volume_le (E := EuclideanSpace ℝ (Fin 3))
      (Tube.gridScale_le_one hδ1 (Tube.ssfGridLen δ) k) (𝒰.cover.tube k j)
    rw [hrank] at hvol
    have hvol' : volume (𝒰.cover.tube k j).carrier
        ≤ ((Tube.volume_le.C 3 : NNReal) : ENNReal)
          * ((Tube.gridScale δ (Tube.ssfGridLen δ) k : NNReal) : ENNReal) ^ (2 : ℕ) := by
      simpa using hvol
    calc ENNReal.ofReal κ * volume (𝒰.cover.tube k j).carrier
        ≤ ENNReal.ofReal κ * (((Tube.volume_le.C 3 : NNReal) : ENNReal)
            * ((Tube.gridScale δ (Tube.ssfGridLen δ) k : NNReal) : ENNReal) ^ (2 : ℕ)) :=
          mul_le_mul' le_rfl hvol'
      _ = ENNReal.ofReal κ * ((Tube.volume_le.C 3 : NNReal) : ENNReal)
            * ((Tube.gridScale δ (Tube.ssfGridLen δ) k : NNReal) : ENNReal) ^ (2 : ℕ) := by ring
      _ ≤ ((Tube.le_volume.c 3 : NNReal) : ENNReal)
            * ((Tube.gridScale δ (Tube.ssfGridLen δ) c : NNReal) : ENNReal) ^ (2 : ℕ) := hκ

end FillFromVolume

section WindowBody

universe u

variable {ι : Type u} {δ Cu : NNReal} {s : Finset ι}
  {T : ι → Tube δ (EuclideanSpace ℝ (Fin 3))}

open scoped Classical in
/-- **`le_window_maxDensity` with the per-tube volume floor supplied.** -/
theorem window_field_of_body (𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu)
    {Cstar : ENNReal} {η : ℕ → ℝ} {εd : ℝ} {a b m : ℕ}
    (hK : ∀ ρ : NNReal,
      (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
          * ((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
            / (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)) ^ εd ≤ (ρ : ℝ) →
      (ρ : ℝ) ≤ (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
          * ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
            / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) ^ εd →
      ∀ j ∈ 𝒰.cover.indexSet a,
        ∃ K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)),
          volume K.carrier ≠ 0 ∧ volume K.carrier ≠ ⊤ ∧
          (∀ j' ∈ 𝒰.nodesUnder b a j,
            ((𝒰.cover.tube b j').rescale ρ).toConvexSpaceBody ≤ K) ∧
          ENNReal.ofReal
              (((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ) / (ρ : ℝ)) ^ η (m + 1))
              * volume K.carrier
            ≤ Cstar * (((𝒰.nodesUnder b a j).card : ENNReal)
                * (((Tube.le_volume.c 3 : NNReal) : ENNReal)
                    * ((ρ : NNReal) : ENNReal) ^ (2 : ℕ)))) :
    ∀ ρ : NNReal,
      (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
          * ((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
            / (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)) ^ εd ≤ (ρ : ℝ) →
      (ρ : ℝ) ≤ (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
          * ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
            / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) ^ εd →
      ∀ j ∈ 𝒰.cover.indexSet a,
        ENNReal.ofReal (((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ) / (ρ : ℝ)) ^ η (m + 1))
          ≤ Cstar * Kakeya.maxDensity (𝒰.nodesUnder b a j)
              (fun j' => ((𝒰.cover.tube b j').rescale ρ).toConvexSpaceBody) := by
  classical
  have hrank : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  refine window_field_of_card 𝒰 (fun ρ h1 h2 j hj => ?_)
  obtain ⟨K, hK0, hKtop, hsub, hx⟩ := hK ρ h1 h2 j hj
  refine ⟨K, ((Tube.le_volume.c 3 : NNReal) : ENNReal) * ((ρ : NNReal) : ENNReal) ^ (2 : ℕ),
    hK0, hKtop, hsub, fun j' _ => ?_, hx⟩
  have := Tube.le_volume (E := EuclideanSpace ℝ (Fin 3)) ((𝒰.cover.tube b j').rescale ρ)
  rw [hrank] at this
  simpa using this

end WindowBody

section TowerData

universe u

variable {ι : Type u} {δ Cu : NNReal} {s : Finset ι}
  {T : ι → Tube δ (EuclideanSpace ℝ (Fin 3))}

open scoped Classical in
/-- **`hGood` from a family-cardinality bound.** -/
theorem hGood_of_card (𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu) {θ : ℝ}
    (hcard : (s.card : ENNReal)
      ≤ ENNReal.ofReal (((Tube.gridScale δ (Tube.ssfGridLen δ) 0 : ℝ)
          / (Tube.gridScale δ (Tube.ssfGridLen δ) (Tube.ssfGridLen δ) : ℝ)) ^ θ)) :
    towerDensityArrayFibre 𝒰 0 (Tube.ssfGridLen δ)
      ≤ ENNReal.ofReal (((Tube.gridScale δ (Tube.ssfGridLen δ) 0 : ℝ)
          / (Tube.gridScale δ (Tube.ssfGridLen δ) (Tube.ssfGridLen δ) : ℝ)) ^ θ) := by
  classical
  refine towerDensityArrayFibre_le_of_card_le 𝒰 (fun j _ => le_trans ?_ hcard)
  have : (𝒰.assignFibre (Tube.ssfGridLen δ) 0 j).card ≤ s.card := by
    refine le_trans (Finset.card_image_le) ?_
    exact Finset.card_le_card (Finset.filter_subset _ _)
  exact_mod_cast this

open scoped Classical in
/-- **`hcrude` from the source's displayed cardinality estimate (l.2679-2681).** -/
theorem hcrude_of_cardEstimate (𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu)
    {D : ENNReal}
    (hcard : ∀ p c : ℕ, p ≤ c → c ≤ Tube.ssfGridLen δ →
      ∀ j ∈ 𝒰.cover.indexSet p, ((𝒰.assignFibre c p j).card : ENNReal)
        ≤ D * ENNReal.ofReal
            (((Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ)
              / (Tube.gridScale δ (Tube.ssfGridLen δ) c : ℝ)) ^ (4 : ℕ))) :
    ∀ p c : ℕ, p ≤ c → c ≤ Tube.ssfGridLen δ →
      towerDensityArrayFibre 𝒰 p c ≤ D * ENNReal.ofReal
        (((Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ)
          / (Tube.gridScale δ (Tube.ssfGridLen δ) c : ℝ)) ^ (4 : ℕ)) :=
  fun p c hpc hc => towerDensityArrayFibre_le_of_card_le 𝒰 (hcard p c hpc hc)

end TowerData

section Thresholds

universe u

/-- **The producer's δ-rows, bundled.** -/
def FibreThresholds.{u_1} (β ϖ ε₁ η' : ℝ) (gain dens : ℝ → ℝ) (C Cu : NNReal) (Kl cl : ℕ)
    (δ : NNReal) : Prop :=
  0 < Tube.ssfGridLen δ ∧
  4 * Tube.gridScale δ (Tube.ssfGridLen δ) 1 ≤ 1 ∧
  (Cu : ENNReal) * fibreChainConst.{u_1} ^ (ML2Spine.spineCount ϖ ε₁ + 1)
    ≤ (C : ENNReal) * StickyKakeya.totalLoss C Kl cl δ ∧
  (Cu : ENNReal) ≤ (δ : ENNReal) ^ (-(2 * η')) ∧
  (C : ENNReal) * StickyKakeya.totalLoss C Kl cl δ
    ≤ (δ : ENNReal) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens / 20))

/-- **The tail lemma: one `Eventually` for the whole bundle.** -/
theorem eventually_fibreThresholds.{u_1} {β ϖ ε₁ η' : ℝ} {gain dens : ℝ → ℝ} {C Cu : NNReal}
    {Kl cl : ℕ} (hη' : 0 < η')
    (hgrid : ∀ᶠ δ : NNReal in nhdsWithin 0 (Set.Ioi 0),
      0 < Tube.ssfGridLen δ ∧ 4 * Tube.gridScale δ (Tube.ssfGridLen δ) 1 ≤ 1)
    (hchain : ∀ᶠ δ : NNReal in nhdsWithin 0 (Set.Ioi 0),
      (Cu : ENNReal) * fibreChainConst.{u_1} ^ (ML2Spine.spineCount ϖ ε₁ + 1)
        ≤ (C : ENNReal) * StickyKakeya.totalLoss C Kl cl δ)
    (hnu : ∀ᶠ δ : NNReal in nhdsWithin 0 (Set.Ioi 0),
      (C : ENNReal) * StickyKakeya.totalLoss C Kl cl δ
        ≤ (δ : ENNReal) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens / 20))) :
    ∀ᶠ δ : NNReal in nhdsWithin 0 (Set.Ioi 0),
      FibreThresholds.{u_1} β ϖ ε₁ η' gain dens C Cu Kl cl δ := by
  filter_upwards [hgrid, hchain, hnu,
    Kakeya.VeryNotSticky.eventually_ennreal_le_rpow_neg (K := (Cu : ENNReal))
      ENNReal.coe_ne_top (by linarith : (0 : ℝ) < 2 * η')] with δ hg hc hn hcu
  exact ⟨hg.1, hg.2, hc, hcu, hn⟩

end Thresholds

section TightProducer

universe u

variable {ι : Type u} {δ Cu : NNReal} {v : Finset ι}
  {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}

open scoped Classical in
/-- **`RefinedSupplyAt` with the rows read only on the refined tower.** -/
theorem refinedSupplyAt_of_tightRows {β ϖ ε₁ η' κ : ℝ} {gain dens : ℝ → ℝ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    (hη' : 0 < η') (hκ : 0 < κ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    {C : NNReal} {Kl cl : ℕ} {Λf : ℝ≥0∞} {D : ENNReal} (hD1 : 1 ≤ D)
    (hthr : FibreThresholds.{u} β ϖ ε₁ η' gain dens C Cu Kl cl δ)
    {𝒰 : Tube.UniformTubeSet v (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu}
    (hcap : ∀ m : ℕ, η' ≤ ML2Spine.spineDiv ϖ ε₁ ^ 2
      * ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1) / 64)
    (hpass : ∀ (S : Finset ι) (hS : S ⊆ v), S.Nonempty →
      ∀ (Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
        (ht : ∀ i, (Z i).toTube = (T i).toTube) (hh : IsClassHomogeneousOn 𝒰 S),
      ∃ (S' : Finset ι) (hS' : S' ⊆ S)
        (hhom : IsClassHomogeneousOn ((𝒰.restrictOccupied hS hh).retube (funext ht)) S'),
        IsShadedRefinementOf ((𝒰.restrictOccupied hS hh).retube (funext ht)) Λf S Z S' Z ∧
        (∃ Φ : ℕ → ℕ → ENNReal, ∀ p ≤ Tube.ssfGridLen δ, ∀ c ≤ Tube.ssfGridLen δ,
          ∀ j ∈ (refinedHierarchy ((𝒰.restrictOccupied hS hh).retube (funext ht))
              hS' hhom rfl).cover.indexSet p,
          Φ p c ≤ Kakeya.maxDensity
              ((refinedHierarchy ((𝒰.restrictOccupied hS hh).retube (funext ht))
                hS' hhom rfl).assignFibre c p j)
              (fun j' => ((refinedHierarchy ((𝒰.restrictOccupied hS hh).retube (funext ht))
                hS' hhom rfl).cover.tube c j').toConvexSpaceBody) ∧
            Kakeya.maxDensity
              ((refinedHierarchy ((𝒰.restrictOccupied hS hh).retube (funext ht))
                hS' hhom rfl).assignFibre c p j)
              (fun j' => ((refinedHierarchy ((𝒰.restrictOccupied hS hh).retube (funext ht))
                hS' hhom rfl).cover.tube c j').toConvexSpaceBody)
              ≤ (C : ENNReal) * StickyKakeya.totalLoss C Kl cl δ * Φ p c) ∧
        FibreWindowRows β ϖ ε₁ η' κ gain dens
          ((C : ENNReal) * StickyKakeya.totalLoss C Kl cl δ) D
          (refinedHierarchy ((𝒰.restrictOccupied hS hh).retube (funext ht)) hS' hhom rfl))
    (hball : ∀ i ∈ v, ((T i).toTube).carrier
      ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    RefinedSupplyAt (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ η' gain dens Λf
      ((Cu : ENNReal) * (fibreChainConst.{u} ^ (ML2Spine.spineCount ϖ ε₁ + 2)
        * (D * ENNReal.ofReal ((δ : ℝ) ^ (-(5 * ML2Spine.spineDiv ϖ ε₁)))))) 𝒰 := by
  classical
  obtain ⟨hLpos, h4, hCstarChain, hCuη, hCstarNu⟩ := hthr
  refine refinedSupplyAt_of_dichotomy (fun S hS hne Z ht hh => ?_)
  obtain ⟨S', hS', hhom, href, ⟨Φ, hband⟩, hGood, hcrude, hwindow, hfill, hclose⟩ :=
    hpass S hS hne Z ht hh
  refine ⟨S', Z, hS', hhom, rfl, href, ?_⟩
  have hS'ne : S'.Nonempty := href.nonempty
  have hball' : ∀ i ∈ S', ((Z i).toTube).carrier
      ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
    intro i hi
    rw [ht i]
    exact hball i (hS (hS' hi))
  rcases isKatzTaoAtEveryScale_or_dividingWindow_spine hβ0 hβ1 hϖ hε₁ hgain hdens hδ0 hδ1
    h4 hLpos _ hS'ne hball' hCstarChain hGood hD1 hcrude hwindow hband with hev | ⟨a, b, m, hwin⟩
  · exact Or.inl hev
  · exact Or.inr ⟨a, b, m, hwin,
      floorHypothesisAt_of_fibreWindow hβ0 hβ1 hϖ hε₁ hgain hdens hη' hκ hδ0 hδ1 h4 _ hS'ne
        hball' hCuη hwin hCstarNu (hcap m) (hfill a b) (hclose a b m)⟩

open scoped Classical in
/-- **`RefinedFloorSupplyAt` from the tightened producer.** -/
theorem refinedFloorSupplyAt_of_tightRows {β ϖ ε₁ η' κ : ℝ} {gain dens : ℝ → ℝ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    (hη' : 0 < η') (hκ : 0 < κ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    {C : NNReal} {Kl cl : ℕ} {Λf : ℝ≥0∞} {D : ENNReal} (hD1 : 1 ≤ D)
    (hthr : FibreThresholds.{u} β ϖ ε₁ η' gain dens C Cu Kl cl δ)
    {𝒰 : Tube.UniformTubeSet v (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu}
    (hcap : ∀ m : ℕ, η' ≤ ML2Spine.spineDiv ϖ ε₁ ^ 2
      * ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1) / 64)
    (hpass : ∀ (S : Finset ι) (hS : S ⊆ v), S.Nonempty →
      ∀ (Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
        (ht : ∀ i, (Z i).toTube = (T i).toTube) (hh : IsClassHomogeneousOn 𝒰 S),
      ∃ (S' : Finset ι) (hS' : S' ⊆ S)
        (hhom : IsClassHomogeneousOn ((𝒰.restrictOccupied hS hh).retube (funext ht)) S'),
        IsShadedRefinementOf ((𝒰.restrictOccupied hS hh).retube (funext ht)) Λf S Z S' Z ∧
        (∃ Φ : ℕ → ℕ → ENNReal, ∀ p ≤ Tube.ssfGridLen δ, ∀ c ≤ Tube.ssfGridLen δ,
          ∀ j ∈ (refinedHierarchy ((𝒰.restrictOccupied hS hh).retube (funext ht))
              hS' hhom rfl).cover.indexSet p,
          Φ p c ≤ Kakeya.maxDensity
              ((refinedHierarchy ((𝒰.restrictOccupied hS hh).retube (funext ht))
                hS' hhom rfl).assignFibre c p j)
              (fun j' => ((refinedHierarchy ((𝒰.restrictOccupied hS hh).retube (funext ht))
                hS' hhom rfl).cover.tube c j').toConvexSpaceBody) ∧
            Kakeya.maxDensity
              ((refinedHierarchy ((𝒰.restrictOccupied hS hh).retube (funext ht))
                hS' hhom rfl).assignFibre c p j)
              (fun j' => ((refinedHierarchy ((𝒰.restrictOccupied hS hh).retube (funext ht))
                hS' hhom rfl).cover.tube c j').toConvexSpaceBody)
              ≤ (C : ENNReal) * StickyKakeya.totalLoss C Kl cl δ * Φ p c) ∧
        FibreWindowRows β ϖ ε₁ η' κ gain dens
          ((C : ENNReal) * StickyKakeya.totalLoss C Kl cl δ) D
          (refinedHierarchy ((𝒰.restrictOccupied hS hh).retube (funext ht)) hS' hhom rfl))
    (hball : ∀ i ∈ v, ((T i).toTube).carrier
      ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (hno : ∀ {S' : Finset ι} {W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
      (V : Tube.UniformTubeSet S' (fun i => (W i).toTube) (Tube.ssfGridLen δ) Cu),
      ¬ V.IsKatzTaoAtEveryScale ((Cu : ENNReal)
        * (fibreChainConst.{u} ^ (ML2Spine.spineCount ϖ ε₁ + 2)
          * (D * ENNReal.ofReal ((δ : ℝ) ^ (-(5 * ML2Spine.spineDiv ϖ ε₁))))))) :
    RefinedFloorSupplyAt (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ η' gain dens Λf 𝒰 :=
  refinedFloorSupplyAt_of_refinedSupplyAt
    (refinedSupplyAt_of_tightRows hβ0 hβ1 hϖ hε₁ hgain hdens hη' hκ hδ0 hδ1 hD1 hthr hcap
      hpass hball) hno

end TightProducer

section Controls

universe u

variable {ι : Type u} {δ Cu : NNReal} {s : Finset ι}
  {T : ι → Tube δ (EuclideanSpace ℝ (Fin 3))}

/-- **Firing control: the per-cell volume floor is load-bearing in `fillAt_of_volume`.** -/
theorem fillAt_of_volume_vacuous_at_zero
    (𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu) {κ : ℝ} {k : ℕ} {j : ι}
    (hk0 : volume (𝒰.cover.tube k j).carrier ≠ 0)
    (hκ : ENNReal.ofReal κ * volume (𝒰.cover.tube k j).carrier ≤ 0) :
    ENNReal.ofReal κ = 0 := by
  rw [nonpos_iff_eq_zero, mul_eq_zero] at hκ
  exact hκ.resolve_right hk0

/-- **Control: the volume route caps `κ` below `1`.** -/
theorem fillAt_of_gridScale_kappa_cap {κ : ℝ} {k : ℕ}
    (hκ : ENNReal.ofReal κ
        * ((Tube.volume_le.C 3 : NNReal) : ENNReal)
        * ((Tube.gridScale δ (Tube.ssfGridLen δ) k : NNReal) : ENNReal) ^ (2 : ℕ)
      ≤ ((Tube.le_volume.c 3 : NNReal) : ENNReal)
        * ((Tube.gridScale δ (Tube.ssfGridLen δ) k : NNReal) : ENNReal) ^ (2 : ℕ))
    (hpos : ((Tube.gridScale δ (Tube.ssfGridLen δ) k : NNReal) : ENNReal) ^ (2 : ℕ) ≠ 0)
    (htop : ((Tube.gridScale δ (Tube.ssfGridLen δ) k : NNReal) : ENNReal) ^ (2 : ℕ) ≠ ⊤) :
    ENNReal.ofReal κ * ((Tube.volume_le.C 3 : NNReal) : ENNReal)
      ≤ ((Tube.le_volume.c 3 : NNReal) : ENNReal) := by
  refine (ENNReal.mul_le_mul_iff_right hpos htop).mp ?_
  calc ((Tube.gridScale δ (Tube.ssfGridLen δ) k : NNReal) : ENNReal) ^ (2 : ℕ)
        * (ENNReal.ofReal κ * ((Tube.volume_le.C 3 : NNReal) : ENNReal))
      = ENNReal.ofReal κ * ((Tube.volume_le.C 3 : NNReal) : ENNReal)
        * ((Tube.gridScale δ (Tube.ssfGridLen δ) k : NNReal) : ENNReal) ^ (2 : ℕ) := by ring
    _ ≤ ((Tube.le_volume.c 3 : NNReal) : ENNReal)
        * ((Tube.gridScale δ (Tube.ssfGridLen δ) k : NNReal) : ENNReal) ^ (2 : ℕ) := hκ
    _ = ((Tube.gridScale δ (Tube.ssfGridLen δ) k : NNReal) : ENNReal) ^ (2 : ℕ)
        * ((Tube.le_volume.c 3 : NNReal) : ENNReal) := by ring

end Controls

end Kakeya.ML2Core

end

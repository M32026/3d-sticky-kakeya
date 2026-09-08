/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSiteEDSplit

/-!
# The source's covering bridge, `lem:defect-covering-bridge`

This leaf transcribes `lem:defect-covering-bridge` of the refined source
(`prof_ma_refined/260115_kakeyadetailedproofv3_revised_detailed.tex`, statement l.5484–5547,
proof l.5549–5672, and its *use* at l.4596–4617), which is the producer of the count floor that
`Kakeya.ML2Core.edCover_of_sourceBridge` (`Reduction/SpineSiteEDSplit.lean`) consumes at the six
middle-factor sites of `Kakeya.ML2Assembly.GeometricCoreAt`.

## What the source lemma says, and what is transcribed here

The source concludes, for **every** finite family `𝕎` of exact `σ`-tubes covering `𝕍₀`
(l.5541–5546, `eq:defect-arbitrary-cover`),

  `#𝕎 ≥ θ · σ^{-2-2ζ}`.

That is exactly the shape `edCover_of_sourceBridge` binds: `θ ρ * ρ^{-2-2ζ'} ≤ #t`.  The passage
to the sites' bare slot `ρ^{-2-ζ'} ≤ #t` is the ordering `ρ^{ζ'} ≤ θ ρ`, already existing as
`Kakeya.ML2Core.floor_absorb_of_rpow_le` with its firing control
`Kakeya.ML2Core.not_floor_absorb_without_ordering`.

The proof of the source lemma is a chain of four counting steps and one arithmetic absorption,
and this leaf transcribes it in that order:

* `bridge_cellCount_chain` — the counting core, l.5628–5663.  Four pigeonholes:
  (i)  `#𝕍₀ ≤ #𝕌₀`      the cover map `ϖ` is onto (l.5628–5631);
  (iii) `#𝕌 ≤ Afib · #𝕍`  its fibres are at most `5000⁶A` (`eq:defect-bridge-cover-map`);
  (vi) `D · #𝕋_m⟨S_a⟩ ≤ #𝕋_b⟨S_a⟩` and (v) `#𝕌₀ ≤ 2D · #ℋ_m`  descendant regularity
       (l.5528–5530, l.5639–5645);
  (vii) `#ℋ_m ≤ A₁ · #𝕎`  line-based essential distinctness charges `A₁` cells to one `W`
       (l.5657–5658).
  Output: `θθ₀/(2·Afib·A₁) · #𝕋_m⟨S_a⟩ ≤ #𝕎`, the source's l.5662–5664 before the floor.
* `bridge_charge_fibre_of_lineED` — pigeonhole (vii)'s hypothesis, derived from the tree's
  `Kakeya.VeryNotSticky.IsLineEssDistinctAt 5 A₁` on the level-`m` family, given the placement
  `BridgeTransversePlacement`.
* `bridge_absorb_of_scale_test` — the arithmetic absorption, l.5666–5669: the second scale test
  of `eq:defect-bridge-scale-tests` together with `2+4ζ ≤ 3` absorbs the grid loss `δ^{1/M}` and
  every fixed constant, turning the counting output into `θ σ^{-2-2ζ}`.
* `defectCoveringBridge` — the composition, `eq:defect-arbitrary-cover`.
* `bridge_ordering_of_thresholds` — **not** part of the lemma: the *call site*'s derivation of the
  ordering `σ^ζ ≤ θ`, l.4618–4632.  The source derives it there from
  `θ = κδ^{6η_c} ≥ δ^{7η_c}`, `σ ≤ δ^{εε_sc/2}` and `7η_c ≤ εε_scζ/2`; it is **not** stated
  separately and **not** arranged by the selection at l.4486–4500.  This answers the sixth input.

## The named hypotheses and their owners

Each is stated at its own family / shading / level pair; the pair is named in every docstring
below, because that column is where this run's defects lived.

* `hret` : `θ₀ * #𝕋_b⟨S_a⟩ ≤ #𝕌`, `eq:defect-bridge-retention` l.5496–5499 with
  `θ₀ ≥ δ^{6η_c}` l.4497.  Family `𝕌 ⊆ 𝕋_b⟨S_a⟩`, pair `(p,b)`.
  Owner **`w325gen`** (`SpineMassCoupledSelection.lean`, R0b).
* `hDlo` / `hDhi` : `#𝕋_b⟨S⟩ ∈ [D, 2D]`, l.5528–5530.  Family `S ∈ 𝕋_m⟨S_a⟩`, pair `(m,b)`.
  Owner **`w325gen`** (`SpineJointStatisticBin.lean`).
* `hϖsurj` / `hϖfib` : `eq:defect-bridge-cover-map` l.5512–5515.  Family `ϖ : 𝕌 ↠ 𝕍`, level `b`,
  after normalizing `S_a`.  Owner: the canonical exact cover.
* `hfloor` : `(ρ_a/ρ_m)^{2+4ζ} ≤ #𝕋_m⟨S_a⟩`, `eq:defect-bridge-floor` l.5518–5521, which is
  `eq:ml2-count-floor` l.4478–4481.  Family `𝕋_m⟨S_a⟩`, pair `(a,m)` = the source's `(p,m)`.
  existing as the last conjunct of `Kakeya.ML2Core.FloorHypothesisAt`.
* `hgrid` : `δ^{1/M}/(56σ) ≤ ρ_a/ρ_m`, l.5590–5622 (the window location of `m`).  The radius
  grid alone; grid arithmetic, this leaf's hypothesis.
* `hchg` / `hA₁fib` : the charging, l.5653–5658.  Family `ℋ_m ⊆ 𝕋_m⟨S_a⟩` against `𝕎`.
  Supplied by `bridge_charge_fibre_of_lineED` from `BridgeTransversePlacement` plus the tree's
  `Kakeya.VeryNotSticky.IsLineEssDistinctAt 5 A₁` at level `m`.  Its anisotropic half is proved
  in `Reduction/SpineBridgePullbackGrid.lean` — see below.
* `htest` : the second scale test, `eq:defect-bridge-scale-tests` l.5538–5539.  Scalars only;
  owner: the parameter selection.

## Input 3, resolved: the transverse estimate is an *upper* bound

The check in `S9FIBRE_priv/PATCH_MANIFEST_EDSPLIT.txt` asked whether the bridge needs a *lower*
transverse estimate, which the tree's the estimate pull-backs (packing upper bounds) could not give.
Read at l.5573–5588, the source's transverse estimate is
`L^{-1}(W) ⊆ 𝓛_W + B̄(0, 56ρ_aσ)` — an **inclusion**, i.e. an upper bound on the transverse
extent of the pulled-back covering tube.  It is not used to bound `#𝕎` from below directly; the
lower bound on `#𝕎` comes entirely from the four pigeonholes.  The inclusion is used only to
*place* the named `m`-ancestor of a covered `b`-child in a `5ρ_m`-neighbourhood of one affine
line (l.5653–5656), so that `A₁`-line-essential-distinctness caps the charging fibre.  So the
check's worry does not apply: an upper bound is the right direction, and the tree's pull-backs
are the right *kind* of estimate — but not the same statement, see below.

## The last open row — now CLOSED in the companion leaf

`BridgeAnisotropicPullback` — the source's `eq:defect-pullback-line` (l.5573–5586) — was the
single step of the proof with no tree analogue.  It is **proved** in
`Reduction/SpineBridgePullbackGrid.lean` as
`Kakeya.ML2Core.exists_bridgeAnisotropicPullback`, together with `hgrid`
(`bridgeGrid_hgrid_of_maximal`).  The measurement below is why it had to be built rather than
found, and is kept as the record of that search.  It is *not* the whole of
`BridgeTransversePlacement`: the second half of that placement, the comparison of the two unit
cores (l.5655), **is** existing, as `Kakeya.VeryNotSticky.carrier_subset_lineNbhd`, and is
re-exported here as `bridge_placement_of_coreComparison`, which pins the exact budget the open
row must meet — position error plus direction error at most `4ρ_m`.

Search evidence for the negative half (tree grep with a firing control, plus `leansearch`):
producers of `_ ⊆ lineNbhd _ _ _` anywhere in `Kakeya` are exactly `Conjunct6LineED.lean`
(`carrier_subset_lineNbhd`, `carrier_subset_own_lineNbhd`, and the maximal-separated-set charging
inside `card_le_lineEDConstant_of_lineEDFamily`) and one *negative* statement in
`SpineFloorShapeMeasurements.lean`; the control grep on `lineNbhd` alone returns seven files, so
the scan is not blind.  The two candidates the check named,
`Kakeya.ML2Reduction.carrier_subset_dilate_of_normaliseBody_subset_dilate`  and
`card_le_centringCoverFibreConstant_of_normaliseBody`, are respectively a containment in a
**dilated tube** under the **isotropic** `normaliseBody` contraction `8`, and a fibre-count
ceiling.  Neither is the anisotropic estimate `L₀^{-1}y = 8(y_∥ + ρ_a y_⊥)` of l.5555, and neither
produces an affine line.

Exact Lean goal of the open row, at the source's own constants:

  `‖d‖ = 1 ∧ Lsymm '' Wtube.carrier ⊆ Kakeya.VeryNotSticky.lineNbhd p d (56 * ρa * (σ : ℝ))`

## Input 2, decided from the source

The source uses "line-based essential distinctness" at the level-`m` family and at
neighbourhood radius `5ρ_m` (l.5490–5491, l.5655–5658).  In the tree that is
`Kakeya.VeryNotSticky.IsLineEssDistinctAt 5 A₁ 𝕋_m 𝕋cell`, i.e. the site-4 shape
`IsLineEssDistinctAt _ A t W` and **not** `LineEDLevelsAt C₃ … 𝒰.tubeUniform.activeRestrict`
, which is a datum about *every* level of a hierarchy at the two-tube overlap radius `C₃`.
`IsLineEssDistinctAt.mono_radius` converts the `C₃` form into the `5` form when `5 ≤ C₃`, so the
the estimate datum is usable, but the shape the bridge binds is the single-level one.

## The `hfac` seam

Nothing in this leaf needs `w308gen`'s `(a,b) → (p,b)` seam: the bridge is stated for an abstract
pair of levels and an abstract ancestor map `anc`, so the reindexing from the source's
`(a,b)` to the run's `(p,b)` is discharged by *instantiating* `anc`, not by any statement here.
That is deliberate — the check's item 1 ("a different family, scale variable and exponent") is the
bridge's content, and abstracting the level pair is how the content is transcribed.
-/

@[expose] public section

open Real

namespace Kakeya.ML2Core

universe u

/-! ### Layer A: the arithmetic absorption (source l.5666-5669) -/

/-- **The source's final absorption**, l.5666–5669: "Because `2+4ζ ≤ 3`, the second inequality
in `eq:defect-bridge-scale-tests` absorbs both the grid loss and all fixed constants, leaving
`#𝕎 ≥ θσ^{-2-2ζ}`."  The grid loss is `q = δ^{1/M}` (l.5622); the fixed constants are
`2·5000⁶` from the two fibre bounds and `56^{2+4ζ}` from the transverse radius, and
`2·5000⁶·56³ ≤ 10³⁰` is the source's slack.  Scalars only — no family. -/
theorem bridge_absorb_of_scale_test
    {σ q θ θ₀ A A₁ ζ N : ℝ}
    (hσ0 : 0 < σ) (hζ0 : 0 < ζ) (hζ : ζ ≤ 1 / 4)
    (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hθ0 : 0 < θ) (hθ₀0 : 0 < θ₀)
    (hA : 1 ≤ A) (hA₁ : 1 ≤ A₁)
    (htest : σ ^ (2 * ζ) ≤ θ₀ * q ^ (3 : ℝ) / (10 ^ 30 * A * A₁))
    (hcount : θ * θ₀ / (2 * 5000 ^ 6 * A * A₁) * (q / (56 * σ)) ^ (2 + 4 * ζ) ≤ N) :
    θ * σ ^ (-2 - 2 * ζ) ≤ N := by
  refine le_trans ?_ hcount
  set E : ℝ := 2 + 4 * ζ with hEdef
  have hE3 : E ≤ 3 := by rw [hEdef]; linarith
  have hA0 : (0:ℝ) < A := lt_of_lt_of_le one_pos hA
  have hA₁0 : (0:ℝ) < A₁ := lt_of_lt_of_le one_pos hA₁
  have hσE : (0:ℝ) < σ ^ E := Real.rpow_pos_of_pos hσ0 _
  have hqE : (0:ℝ) < q ^ E := Real.rpow_pos_of_pos hq0 _
  have h56E : (0:ℝ) < (56:ℝ) ^ E := Real.rpow_pos_of_pos (by norm_num) _
  have hlhs : σ ^ (-2 - 2 * ζ) = σ ^ (2 * ζ) * (σ ^ E)⁻¹ := by
    rw [← Real.rpow_neg hσ0.le, ← Real.rpow_add hσ0]
    congr 1
    rw [hEdef]; ring
  have hrhs : (q / (56 * σ)) ^ E = q ^ E * ((56:ℝ) ^ E)⁻¹ * (σ ^ E)⁻¹ := by
    rw [Real.div_rpow hq0.le (by positivity), Real.mul_rpow (by norm_num) hσ0.le]
    field_simp
  have hq3E : q ^ (3:ℝ) ≤ q ^ E := Real.rpow_le_rpow_of_exponent_ge hq0 hq1 hE3
  have h56 : (56:ℝ) ^ E ≤ (56:ℝ) ^ (3:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hE3
  have h563 : (56:ℝ) ^ (3:ℝ) = 175616 := by
    rw [show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have hden : 2 * 5000 ^ 6 * A * A₁ * (56:ℝ) ^ E ≤ 10 ^ 30 * A * A₁ := by
    have hc : (56:ℝ) ^ E ≤ 175616 := by rw [← h563]; exact h56
    nlinarith [mul_pos hA0 hA₁0]
  have hnum : θ * θ₀ * q ^ (3:ℝ) ≤ θ * θ₀ * q ^ E := by
    have := mul_le_mul_of_nonneg_left hq3E (mul_pos hθ0 hθ₀0).le
    linarith
  have key : θ * σ ^ (2 * ζ)
      ≤ θ * θ₀ / (2 * 5000 ^ 6 * A * A₁) * q ^ E * ((56:ℝ) ^ E)⁻¹ := by
    have h1 : θ * σ ^ (2 * ζ) ≤ θ * θ₀ * q ^ (3:ℝ) / (10 ^ 30 * A * A₁) := by
      have := mul_le_mul_of_nonneg_left htest hθ0.le
      calc θ * σ ^ (2 * ζ) ≤ θ * (θ₀ * q ^ (3:ℝ) / (10 ^ 30 * A * A₁)) := this
        _ = θ * θ₀ * q ^ (3:ℝ) / (10 ^ 30 * A * A₁) := by ring
    have h2 : θ * θ₀ * q ^ (3:ℝ) / (10 ^ 30 * A * A₁)
        ≤ θ * θ₀ * q ^ E / (2 * 5000 ^ 6 * A * A₁ * (56:ℝ) ^ E) := by
      gcongr
    calc θ * σ ^ (2 * ζ) ≤ θ * θ₀ * q ^ (3:ℝ) / (10 ^ 30 * A * A₁) := h1
      _ ≤ θ * θ₀ * q ^ E / (2 * 5000 ^ 6 * A * A₁ * (56:ℝ) ^ E) := h2
      _ = θ * θ₀ / (2 * 5000 ^ 6 * A * A₁) * q ^ E * ((56:ℝ) ^ E)⁻¹ := by
          field_simp
  calc θ * σ ^ (-2 - 2 * ζ) = (θ * σ ^ (2 * ζ)) * (σ ^ E)⁻¹ := by rw [hlhs]; ring
    _ ≤ (θ * θ₀ / (2 * 5000 ^ 6 * A * A₁) * q ^ E * ((56:ℝ) ^ E)⁻¹) * (σ ^ E)⁻¹ :=
        mul_le_mul_of_nonneg_right key (by positivity)
    _ = θ * θ₀ / (2 * 5000 ^ 6 * A * A₁) * (q / (56 * σ)) ^ E := by rw [hrhs]; ring

/-! ### Layer B: the counting core (source l.5628-5663) -/

open scoped Classical in
/-- **The four pigeonholes of the source proof**, l.5628–5663, combined.

Family / level pairs: `hret` is on `𝕌 ⊆ 𝕋_b⟨S_a⟩`; `hϖ*` are on the exact cover `ϖ : 𝕌 ↠ 𝕍`
at level `b` after normalizing `S_a`; `hV0card` is on `𝕍₀ ⊆ 𝕍`; `hDlo`/`hDhi` are descendant
regularity for the pair `(m,b)`; `hchg`/`hA₁fib` are the charging of `ℋ_m = anc(𝕌₀)` into `𝕎`.

Output: `θθ₀/(2·Afib·A₁) · #𝕋_m⟨S_a⟩ ≤ #𝕎`, which is l.5662–5664 before the count floor is
inserted.  `D` cancels exactly, as the source says at l.5647. -/
theorem bridge_cellCount_chain
    {ιU ιV ιM ιW : Type*}
    (Tb U : Finset ιU) (V V0 : Finset ιV) (ϖ : ιU → ιV)
    (Tm : Finset ιM) (anc : ιU → ιM) (W : Finset ιW) (chg : ιM → ιW)
    (Afib A₁ D : ℕ) {θ θ₀ : ℝ}
    (hUsub : U ⊆ Tb)
    (hret : θ₀ * (Tb.card : ℝ) ≤ (U.card : ℝ))
    (hϖmaps : ∀ u ∈ U, ϖ u ∈ V)
    (hϖsurj : ∀ v ∈ V, ∃ u ∈ U, ϖ u = v)
    (hϖfib : ∀ v ∈ V, (U.filter (fun u => ϖ u = v)).card ≤ Afib)
    (hV0 : V0 ⊆ V)
    (hV0card : θ * (V.card : ℝ) ≤ (V0.card : ℝ))
    (hancmaps : ∀ u ∈ Tb, anc u ∈ Tm)
    (hDlo : ∀ x ∈ Tm, D ≤ (Tb.filter (fun u => anc u = x)).card)
    (hDhi : ∀ x ∈ Tm, (Tb.filter (fun u => anc u = x)).card ≤ 2 * D)
    (hchg : ∀ x ∈ (U.filter (fun u => ϖ u ∈ V0)).image anc, chg x ∈ W)
    (hA₁fib : ∀ w ∈ W,
      (((U.filter (fun u => ϖ u ∈ V0)).image anc).filter (fun x => chg x = w)).card ≤ A₁)
    (hD0 : 0 < D) (hAfib0 : 0 < Afib) (hA₁0 : 0 < A₁) (hθ0 : 0 < θ) (hθ₀0 : 0 < θ₀) :
    θ * θ₀ / (2 * Afib * A₁) * (Tm.card : ℝ) ≤ (W.card : ℝ) := by
  classical
  set U0 : Finset ιU := U.filter (fun u => ϖ u ∈ V0) with hU0
  set Hm : Finset ιM := U0.image anc with hHm
  have hU0sub : U0 ⊆ U := Finset.filter_subset _ _
  -- (i)  #V0 ≤ #U0
  have step1 : V0.card ≤ U0.card := by
    have hsub : V0 ⊆ U0.image ϖ := by
      intro v hv
      obtain ⟨u, hu, huv⟩ := hϖsurj v (hV0 hv)
      exact Finset.mem_image.mpr ⟨u, Finset.mem_filter.mpr ⟨hu, by rw [huv]; exact hv⟩, huv⟩
    exact le_trans (Finset.card_le_card hsub) (Finset.card_image_le)
  -- (iii) #U ≤ Afib * #V
  have step2 : U.card ≤ Afib * V.card :=
    Finset.card_le_mul_card_image_of_maps_to hϖmaps Afib hϖfib
  -- (vi) D * #Tm ≤ #Tb
  have step3 : D * Tm.card ≤ Tb.card :=
    Finset.mul_card_image_le_card_of_maps_to hancmaps D hDlo
  -- (v)  #U0 ≤ 2D * #Hm
  have step4 : U0.card ≤ 2 * D * Hm.card := by
    refine Finset.card_le_mul_card_image U0 (2 * D) ?_
    intro x hx
    obtain ⟨u, hu, hux⟩ := Finset.mem_image.mp hx
    have hxTm : x ∈ Tm := by rw [← hux]; exact hancmaps u (hUsub (hU0sub hu))
    refine le_trans (Finset.card_le_card ?_) (hDhi x hxTm)
    exact Finset.filter_subset_filter _ (hU0sub.trans hUsub)
  -- (vii) #Hm ≤ A₁ * #W
  have step5 : Hm.card ≤ A₁ * W.card :=
    Finset.card_le_mul_card_image_of_maps_to hchg A₁ hA₁fib
  -- assemble over ℝ
  have hD0R : (0:ℝ) < D := by exact_mod_cast hD0
  have c1 : θ * θ₀ * (D * (Tm.card : ℝ)) ≤ θ * θ₀ * (Tb.card : ℝ) := by
    have : (D : ℝ) * (Tm.card : ℝ) ≤ (Tb.card : ℝ) := by exact_mod_cast step3
    nlinarith [mul_pos hθ0 hθ₀0]
  have c2 : θ * θ₀ * (Tb.card : ℝ) ≤ θ * (U.card : ℝ) := by nlinarith
  have c3 : θ * (U.card : ℝ) ≤ (Afib : ℝ) * (θ * (V.card : ℝ)) := by
    have : (U.card : ℝ) ≤ (Afib : ℝ) * (V.card : ℝ) := by exact_mod_cast step2
    nlinarith
  have c4 : (Afib : ℝ) * (θ * (V.card : ℝ)) ≤ (Afib : ℝ) * (V0.card : ℝ) := by
    have hA : (0:ℝ) ≤ (Afib : ℝ) := Nat.cast_nonneg _
    exact mul_le_mul_of_nonneg_left hV0card hA
  have c5 : (Afib : ℝ) * (V0.card : ℝ) ≤ (Afib : ℝ) * (2 * D * A₁ * (W.card : ℝ)) := by
    have h : (V0.card : ℝ) ≤ 2 * (D:ℝ) * (A₁:ℝ) * (W.card : ℝ) := by
      have h1 : (V0.card : ℝ) ≤ (2 * D : ℕ) * (Hm.card : ℝ) := by
        exact_mod_cast le_trans step1 step4
      have h2 : (Hm.card : ℝ) ≤ (A₁ : ℝ) * (W.card : ℝ) := by exact_mod_cast step5
      have hDA : (0:ℝ) ≤ ((2 * D : ℕ) : ℝ) := Nat.cast_nonneg _
      have := mul_le_mul_of_nonneg_left h2 hDA
      push_cast at h1 this ⊢
      linarith
    exact mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)
  have chain : θ * θ₀ * (D * (Tm.card : ℝ))
      ≤ (Afib : ℝ) * (2 * (D:ℝ) * (A₁:ℝ) * (W.card : ℝ)) := by
    calc θ * θ₀ * (D * (Tm.card : ℝ)) ≤ θ * θ₀ * (Tb.card : ℝ) := c1
      _ ≤ θ * (U.card : ℝ) := c2
      _ ≤ (Afib : ℝ) * (θ * (V.card : ℝ)) := c3
      _ ≤ (Afib : ℝ) * (V0.card : ℝ) := c4
      _ ≤ (Afib : ℝ) * (2 * (D:ℝ) * (A₁:ℝ) * (W.card : ℝ)) := c5
  -- cancel D
  have hcancel : θ * θ₀ * (Tm.card : ℝ) ≤ 2 * (Afib : ℝ) * (A₁ : ℝ) * (W.card : ℝ) := by
    have := chain
    nlinarith [hD0R]
  have hAfibR : (0:ℝ) < Afib := by exact_mod_cast hAfib0
  have hA₁R : (0:ℝ) < A₁ := by exact_mod_cast hA₁0
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith [hcancel]

/-! ### The one open geometric row -/

/-- **`BridgeTransversePlacement` — the transverse pull-back placement**, the single step of the
source's proof with no tree analogue.

Source: `eq:defect-pullback-line` (l.5583–5586), `L^{-1}(W) ⊆ 𝓛_W + B̄(0,56ρ_aσ)`, combined with
l.5653–5656, "the choice of `m` and comparison of the two unit cores place its named `m`-ancestor
in a fixed `5ρ_m`-neighbourhood of `𝓛_W`".

Family / level pair: `ℋ_m ⊆ 𝕋_m⟨S_a⟩` (the surviving named `m`-cells), charged against the
covering family `𝕎` at radius `σ`; the neighbourhood radius is `5ρ_m`, the **cell** radius, not
`σ` and not `ρ_a`. -/
def BridgeTransversePlacement {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E] {ιM ιW : Type*} {ρm : NNReal} (Hm : Finset ιM) (Tcell : ιM → Tube ρm E)
    (W : Finset ιW) (chg : ιM → ιW) (pt dir : ιW → E) : Prop :=
  ∀ x ∈ Hm, chg x ∈ W ∧
    (Tcell x).carrier ⊆ Kakeya.VeryNotSticky.lineNbhd (pt (chg x)) (dir (chg x)) (5 * (ρm : ℝ))

/-- **The open row, cut down to the one step with no tree analogue.**

`BridgeTransversePlacement` decomposes into two halves at `carrier_subset_lineNbhd`:

* the **core comparison** (source l.5655, "comparison of the two unit cores") — existing, as
  `Kakeya.VeryNotSticky.carrier_subset_lineNbhd`, and re-exported as
  `bridge_placement_of_coreComparison` below with the numerical slack the source's `5ρ_m` leaves;
* the **anisotropic inverse-map estimate** `eq:defect-pullback-line` (l.5573–5586) — this `def`,
  which is what has no tree analogue.

Measured, not asserted.  What the tree has is
`Kakeya.ML2Reduction.carrier_subset_dilate_of_normaliseBody_subset_dilate` : it pulls a
containment back through `normaliseBody`, whose contraction is the **isotropic** factor `8`, and
lands in a `c₀`-**dilate of a tube**, not in a line neighbourhood.  The source's `L` is
anisotropic — `L₀y = ⅛(y_∥ + ρ_a^{-1}y_⊥)`, l.5553 — and its inverse `L₀^{-1}y = 8(y_∥ + ρ_ay_⊥)`
is what produces the radius `56ρ_aσ` (l.5578–5581).  the estimate,
`card_le_centringCoverFibreConstant_of_normaliseBody`, is a fibre-count ceiling and is not this
statement either.  A grep over the whole tree for
producers of `_ ⊆ lineNbhd _ _ _` returns only `Conjunct6LineED.lean` (the core comparison and a
tube inside its own `5σ`-neighbourhood) and one *negative* result in
`SpineFloorShapeMeasurements.lean`; none of them mentions an anisotropic inverse. -/
def BridgeAnisotropicPullback {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E] {σ : NNReal} (Lsymm : E → E) (ρa : ℝ) (Wtube : Tube σ E) (p d : E) : Prop :=
  ‖d‖ = 1 ∧
    Lsymm '' Wtube.carrier ⊆ Kakeya.VeryNotSticky.lineNbhd p d (56 * ρa * (σ : ℝ))

/-- **The existing half of the placement**: `Kakeya.VeryNotSticky.carrier_subset_lineNbhd` at the
source's radius `5ρ_m` (l.5655–5656).  Stating it here fixes the *exact* budget the open row
`BridgeAnisotropicPullback` has to meet: the position error `εp` and the direction error `εd` of
the named `m`-ancestor's core against `𝓛_W` must together be at most `4ρ_m`.  That inequality,
and nothing else, is what l.5653–5656 asserts and what is required as a hypothesis. -/
theorem bridge_placement_of_coreComparison {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E]
    [BorelSpace E] [ProperSpace E]
    {ρm : NNReal} (Q : Tube ρm E) {c p d dp : E} {εp εd : ℝ}
    (hc : c ∈ segment ℝ Q.x Q.y) (hd : d = Q.direction ∨ d = -Q.direction)
    (hp : ‖c - p‖ ≤ εp) (hdd : ‖d - dp‖ ≤ εd)
    (hnum : εp + εd ≤ 4 * (ρm : ℝ)) :
    Q.carrier ⊆ Kakeya.VeryNotSticky.lineNbhd p dp (5 * (ρm : ℝ)) :=
  Kakeya.VeryNotSticky.carrier_subset_lineNbhd Q hc hd hp hdd (by linarith)

open scoped Classical in
/-- **Pigeonhole (vii)'s hypothesis, from the tree's line-based essential distinctness**
(source l.5657–5658: "the `A₁`-essential-distinctness of the level therefore charges at most `A₁`
of the surviving `m`-cells to one `W`").

Family / level pair: `hED` is at level `m` on the full named family `𝕋_m⟨S_a⟩`; the conclusion is
about the sub-family `ℋ_m ⊆ 𝕋_m⟨S_a⟩` and the covering family `𝕎`.  The radius is the source's
`5ρ_m`, which is `Kakeya.VeryNotSticky.IsLineEssDistinctAt 5` at tube radius `ρm`. -/
theorem bridge_charge_fibre_of_lineED {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E]
    {ιM ιW : Type*} {ρm : NNReal} {Tm Hm : Finset ιM} {Tcell : ιM → Tube ρm E}
    {W : Finset ιW} {chg : ιM → ιW} {pt dir : ιW → E} {A₁ : ℕ}
    (hHm : Hm ⊆ Tm)
    (hdir : ∀ w ∈ W, ‖dir w‖ = 1)
    (hplace : BridgeTransversePlacement Hm Tcell W chg pt dir)
    (hED : Kakeya.VeryNotSticky.IsLineEssDistinctAt 5 A₁ Tm Tcell) :
    ∀ w ∈ W, (Hm.filter (fun x => chg x = w)).card ≤ A₁ := by
  classical
  intro w hw
  refine le_trans (Finset.card_le_card ?_) (hED (pt w) (dir w) (hdir w hw))
  intro x hx
  rw [Finset.mem_filter] at hx ⊢
  obtain ⟨hxHm, hxw⟩ := hx
  refine ⟨hHm hxHm, ?_⟩
  have h := (hplace x hxHm).2
  rw [hxw] at h
  exact h

/-! ### The bridge -/

open scoped Classical in
/-- **`lem:defect-covering-bridge`, `eq:defect-arbitrary-cover` (l.5544–5546).**

For every finite family `𝕎` of exact `σ`-tubes covering `𝕍₀`,
`#𝕎 ≥ θ · σ^{-2-2ζ}` — the shape `Kakeya.ML2Core.edCover_of_sourceBridge` binds.

The constants are the source's, copied and not fitted: `2+4ζ` in the count floor, `2+2ζ` in the
conclusion, `5000⁶` in the cover-map fibre bound, `56` in the transverse radius, `10³⁰` in the
second scale test, `2D` in descendant regularity.

Family / level pairs, in the order the hypotheses appear:
`𝕌 ⊆ 𝕋_b⟨S_a⟩` (pair `(a,b)`); `ϖ : 𝕌 ↠ 𝕍` at level `b` after normalizing `S_a`;
`𝕍₀ ⊆ 𝕍`; `anc : 𝕋_b⟨S_a⟩ → 𝕋_m⟨S_a⟩` (pair `(m,b)`); `chg : ℋ_m → 𝕎`;
the count floor on `𝕋_m⟨S_a⟩` (pair `(a,m)`). -/
theorem defectCoveringBridge
    {ιU ιV ιM ιW : Type*}
    (Tb U : Finset ιU) (V V0 : Finset ιV) (ϖ : ιU → ιV)
    (Tm : Finset ιM) (anc : ιU → ιM) (W : Finset ιW) (chg : ιM → ιW)
    (Afib A₁ D : ℕ) {θ θ₀ σ q A ρa ρm ζ : ℝ}
    -- `eq:defect-bridge-retention` (l.5496–5499) : owner `w325gen`, pair `(p,b)`
    (hUsub : U ⊆ Tb)
    (hret : θ₀ * (Tb.card : ℝ) ≤ (U.card : ℝ))
    -- `eq:defect-bridge-cover-map` (l.5512–5515) : the canonical exact cover, level `b`
    (hϖmaps : ∀ u ∈ U, ϖ u ∈ V)
    (hϖsurj : ∀ v ∈ V, ∃ u ∈ U, ϖ u = v)
    (hϖfib : ∀ v ∈ V, (U.filter (fun u => ϖ u = v)).card ≤ Afib)
    (hAfib : (Afib : ℝ) ≤ 5000 ^ 6 * A)
    -- the retained sub-cover `𝕍₀ ⊆ 𝕍` (l.5541–5542)
    (hV0 : V0 ⊆ V)
    (hV0card : θ * (V.card : ℝ) ≤ (V0.card : ℝ))
    -- descendant regularity (l.5528–5530) : owner `w325gen`, pair `(m,b)`
    (hancmaps : ∀ u ∈ Tb, anc u ∈ Tm)
    (hDlo : ∀ x ∈ Tm, D ≤ (Tb.filter (fun u => anc u = x)).card)
    (hDhi : ∀ x ∈ Tm, (Tb.filter (fun u => anc u = x)).card ≤ 2 * D)
    -- the charging map (l.5653–5658) : `BridgeTransversePlacement` + line-ED supply these
    (hchg : ∀ x ∈ (U.filter (fun u => ϖ u ∈ V0)).image anc, chg x ∈ W)
    (hA₁fib : ∀ w ∈ W,
      (((U.filter (fun u => ϖ u ∈ V0)).image anc).filter (fun x => chg x = w)).card ≤ A₁)
    -- `eq:defect-bridge-floor` (l.5518–5521) = `eq:ml2-count-floor` (l.4478–4481), pair `(a,m)`
    (hfloor : (ρa / ρm) ^ (2 + 4 * ζ) ≤ (Tm.card : ℝ))
    -- the window location of `m` (l.5590–5622) : `ρ_a/ρ_m > δ^{1/M}/(56σ)`
    (hgrid : q / (56 * σ) ≤ ρa / ρm)
    -- the second scale test, `eq:defect-bridge-scale-tests` (l.5538–5539)
    (htest : σ ^ (2 * ζ) ≤ θ₀ * q ^ (3 : ℝ) / (10 ^ 30 * A * A₁))
    -- ranges
    (hD0 : 0 < D) (hAfib0 : 0 < Afib) (hA₁0 : 0 < A₁)
    (hθ0 : 0 < θ) (hθ₀0 : 0 < θ₀)
    (hσ0 : 0 < σ) (hζ0 : 0 < ζ) (hζ : ζ ≤ 1 / 4)
    (hq0 : 0 < q) (hq1 : q ≤ 1) (hA1 : 1 ≤ A) :
    θ * σ ^ (-2 - 2 * ζ) ≤ (W.card : ℝ) := by
  classical
  have hA₁R : (1:ℝ) ≤ A₁ := by exact_mod_cast hA₁0
  have hA₁R0 : (0:ℝ) < A₁ := lt_of_lt_of_le one_pos hA₁R
  have hAfibR : (0:ℝ) < Afib := by exact_mod_cast hAfib0
  have hA0 : (0:ℝ) < A := lt_of_lt_of_le one_pos hA1
  -- the counting core
  have hcore := bridge_cellCount_chain Tb U V V0 ϖ Tm anc W chg Afib A₁ D hUsub hret
    hϖmaps hϖsurj hϖfib hV0 hV0card hancmaps hDlo hDhi hchg hA₁fib hD0 hAfib0 hA₁0 hθ0 hθ₀0
  -- the count floor, transported through the grid bound
  have hqσ0 : (0:ℝ) < q / (56 * σ) := by positivity
  have hexp : (0:ℝ) ≤ 2 + 4 * ζ := by linarith
  have hgridpow : (q / (56 * σ)) ^ (2 + 4 * ζ) ≤ (Tm.card : ℝ) :=
    le_trans (Real.rpow_le_rpow hqσ0.le hgrid hexp) hfloor
  -- the constant comparison `Afib ≤ 5000⁶ A`
  have hconst : θ * θ₀ / (2 * 5000 ^ 6 * A * A₁) ≤ θ * θ₀ / (2 * (Afib : ℝ) * A₁) := by
    have hd1 : (0:ℝ) < 2 * (Afib : ℝ) * A₁ := by positivity
    have hd2 : 2 * (Afib : ℝ) * A₁ ≤ 2 * 5000 ^ 6 * A * A₁ := by nlinarith
    exact div_le_div_of_nonneg_left (by positivity) hd1 hd2
  have hcount : θ * θ₀ / (2 * 5000 ^ 6 * A * A₁) * (q / (56 * σ)) ^ (2 + 4 * ζ)
      ≤ (W.card : ℝ) := by
    refine le_trans ?_ hcore
    refine le_trans (mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg hqσ0.le _)) ?_
    exact mul_le_mul_of_nonneg_left hgridpow (by positivity)
  exact bridge_absorb_of_scale_test hσ0 hζ0 hζ hq0 hq1 hθ0 hθ₀0 hA1 hA₁R htest hcount

/-! ### The sixth input: where `σ^ζ ≤ θ` comes from -/

/-- **The ordering `σ^ζ ≤ θ` is derived at the call site, not arranged by the selection.**

Source l.4618–4632: `θ = κδ^{6η_c}` and `κ ≥ δ^{η_c}` give `θ ≥ δ^{7η_c}`; the window gives
`σ ≤ δ^{εε_sc/2}`; and `7η_c ≤ εε_scη₁/32 ≤ εε_scζ/2`.  It is **not** in the selection paragraph
at l.4486–4500 — that paragraph supplies `θ₀ ≥ δ^{6η_c}` only (the bridge's `hret`).  So the
answer to the check's sixth question is: *stated separately, at the call site, and derivable*. -/
theorem bridge_ordering_of_thresholds {δ σ θ ζ ε εsc ηc : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hσ0 : 0 < σ) (hζ0 : 0 ≤ ζ)
    (hσ : σ ≤ δ ^ (ε * εsc / 2))
    (hθ : δ ^ (7 * ηc) ≤ θ)
    (h7 : 7 * ηc ≤ ε * εsc * ζ / 2) :
    σ ^ ζ ≤ θ := by
  refine le_trans (Real.rpow_le_rpow hσ0.le hσ hζ0) (le_trans ?_ hθ)
  rw [← Real.rpow_mul hδ0.le]
  refine Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1 ?_
  linarith [h7]

/-! ### Firing controls -/

/-- **Control for `bridge_absorb_of_scale_test`**: without the second scale test of
`eq:defect-bridge-scale-tests` the absorption fails.  At `σ = 1/2`, `ζ = 1/4`, `q = 1`,
`θ = θ₀ = A = A₁ = 1` and `N = 1` the counting output clears `N`, but `θσ^{-2-2ζ} = 2^{5/2} > 1`.
So the test is load-bearing, and dropping it would be a real defect. -/
theorem not_bridge_absorb_without_scale_test :
    ¬ (∀ σ q θ θ₀ A A₁ ζ N : ℝ, 0 < σ → 0 < ζ → ζ ≤ 1/4 → 0 < q → q ≤ 1 → 0 < θ → 0 < θ₀ →
        1 ≤ A → 1 ≤ A₁ →
        θ * θ₀ / (2 * 5000 ^ 6 * A * A₁) * (q / (56 * σ)) ^ (2 + 4 * ζ) ≤ N →
        θ * σ ^ (-2 - 2 * ζ) ≤ N) := by
  intro h
  have hbase : (0:ℝ) ≤ (1:ℝ) / (56 * (1/2 : ℝ)) := by norm_num
  have hexp : (0:ℝ) ≤ 2 + 4 * (1/4 : ℝ) := by norm_num
  have h1 : ((1:ℝ) / (56 * (1/2 : ℝ))) ^ (2 + 4 * (1/4 : ℝ)) ≤ 1 :=
    Real.rpow_le_one hbase (by norm_num) hexp
  have h0 : (0:ℝ) ≤ ((1:ℝ) / (56 * (1/2 : ℝ))) ^ (2 + 4 * (1/4 : ℝ)) :=
    Real.rpow_nonneg hbase _
  have hc : (1:ℝ) * 1 / (2 * 5000 ^ 6 * 1 * 1)
      * ((1:ℝ) / (56 * (1/2 : ℝ))) ^ (2 + 4 * (1/4 : ℝ)) ≤ 1 :=
    mul_le_one₀ (by norm_num) h0 h1
  have hfire := h (1/2) 1 1 1 1 1 (1/4) 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hc
  have hgt : (1:ℝ) < (1/2 : ℝ) ^ (-2 - 2 * (1/4 : ℝ)) := by
    rw [show (-2 - 2 * (1/4 : ℝ)) = -(5/2 : ℝ) by norm_num, Real.rpow_neg (by norm_num),
      one_lt_inv_iff₀]
    exact ⟨Real.rpow_pos_of_pos (by norm_num) _,
      Real.rpow_lt_one (by norm_num) (by norm_num) (by norm_num)⟩
  simp only [one_mul] at hfire
  linarith

/-! ### The tie: the bridge fills the six middle-factor sites' `hED` slot

`Kakeya.ML2Core.edCover_of_sourceBridge` (`Reduction/SpineSiteEDSplit.lean`) is the existing
consumer; `hED_of_geometricSupplier_of_bridge` is it, re-exported under the name that says what
the supplier's count row now is.  The `example` after it is the shape check that matters: read at
`σ := ρ`, `ζ := ζ'`, `θ := θ ρ`, `𝕎 := t`, the conclusion of `defectCoveringBridge` **is** that
count row, character for character. -/

/-- The six sites' `hED` slot, from a geometric supplier whose count row is the source bridge's
conclusion.  This is `edCover_of_sourceBridge` under a name that records the producer. -/
theorem hED_of_geometricSupplier_of_bridge {b δt δ' : NNReal} {ϖ ζ' : ℝ} {θ : NNReal → ℝ}
    {α : Type u} {s' : Finset α}
    (T₀ : Tube b (EuclideanSpace ℝ (Fin 3)))
    (𝕋 : α → ShadedTube δt (EuclideanSpace ℝ (Fin 3)))
    (hsup : ∀ ρ : NNReal, ρ ∈ Set.Icc
        (δ' ^ (1 - ϖ) / Kakeya.VeryNotSticky.edWindowContractionConstant) (δ' ^ ϖ) →
      ∃ (κ₀ : Type u) (t : Finset κ₀)
        (W : κ₀ → Tube (ρ * b) (EuclideanSpace ℝ (Fin 3))),
        ((t : Set κ₀).Pairwise
          fun j k ↦ _root_.IsEssentiallyDistinct (W j).carrier (W k).carrier) ∧
        (∀ k ∈ t, (W k).carrier ⊆ T₀.carrier) ∧
        (∀ k ∈ t, ∃ i ∈ s', (𝕋 i).carrier ⊆ (W k).carrier) ∧
        θ ρ * (ρ : ℝ) ^ (-2 - 2 * ζ') ≤ (t.card : ℝ))
    (hρ0 : ∀ ρ : NNReal, ρ ∈ Set.Icc
        (δ' ^ (1 - ϖ) / Kakeya.VeryNotSticky.edWindowContractionConstant) (δ' ^ ϖ) → 0 < ρ)
    (hord : ∀ ρ : NNReal, ρ ∈ Set.Icc
        (δ' ^ (1 - ϖ) / Kakeya.VeryNotSticky.edWindowContractionConstant) (δ' ^ ϖ) →
      (ρ : ℝ) ^ ζ' ≤ θ ρ) :
    ∀ ρ : NNReal, ρ ∈ Set.Icc
        (δ' ^ (1 - ϖ) / Kakeya.VeryNotSticky.edWindowContractionConstant) (δ' ^ ϖ) →
      ∃ (κ₀ : Type u) (t : Finset κ₀)
        (W : κ₀ → Tube (ρ * b) (EuclideanSpace ℝ (Fin 3))),
        ((t : Set κ₀).Pairwise
          fun j k ↦ _root_.IsEssentiallyDistinct (W j).carrier (W k).carrier) ∧
        (∀ k ∈ t, (W k).carrier ⊆ T₀.carrier) ∧
        (∀ k ∈ t, ∃ i ∈ s', (𝕋 i).carrier ⊆ (W k).carrier) ∧
        (ρ : ℝ) ^ (-2 - ζ') ≤ (t.card : ℝ) :=
  edCover_of_sourceBridge T₀ 𝕋 hsup hρ0 hord

end Kakeya.ML2Core


/-! ## Ties: the bridge fills the sites' `hED` slot -/

section Ties

open Kakeya Kakeya.ML2Core

variable {b δt δ' : NNReal} {ϖw ζ' : ℝ} {θ : NNReal → ℝ} {α : Type u} {s' : Finset α}
  {T₀ : Tube b (EuclideanSpace ℝ (Fin 3))}
  {𝕋 : α → ShadedTube δt (EuclideanSpace ℝ (Fin 3))}

open scoped Classical in
-- TIE 1 : a supplier whose count row is the source bridge's conclusion fills the six
-- middle-factor sites' `hED` slot, through the existing `edCover_of_sourceBridge`.
example
    (hsup : ∀ ρ : NNReal, ρ ∈ Set.Icc
        (δ' ^ (1 - ϖw) / Kakeya.VeryNotSticky.edWindowContractionConstant) (δ' ^ ϖw) →
      ∃ (κ₀ : Type u) (t : Finset κ₀)
        (W : κ₀ → Tube (ρ * b) (EuclideanSpace ℝ (Fin 3))),
        ((t : Set κ₀).Pairwise
          fun j k ↦ _root_.IsEssentiallyDistinct (W j).carrier (W k).carrier) ∧
        (∀ k ∈ t, (W k).carrier ⊆ T₀.carrier) ∧
        (∀ k ∈ t, ∃ i ∈ s', (𝕋 i).carrier ⊆ (W k).carrier) ∧
        θ ρ * (ρ : ℝ) ^ (-2 - 2 * ζ') ≤ (t.card : ℝ))
    (hρ0 : ∀ ρ : NNReal, ρ ∈ Set.Icc
        (δ' ^ (1 - ϖw) / Kakeya.VeryNotSticky.edWindowContractionConstant) (δ' ^ ϖw) → 0 < ρ)
    (hord : ∀ ρ : NNReal, ρ ∈ Set.Icc
        (δ' ^ (1 - ϖw) / Kakeya.VeryNotSticky.edWindowContractionConstant) (δ' ^ ϖw) →
      (ρ : ℝ) ^ ζ' ≤ θ ρ) : True := by
  have _tie := Kakeya.ML2Core.hED_of_geometricSupplier_of_bridge (ζ' := ζ') (θ := θ) (s' := s') T₀ 𝕋
    hsup hρ0 hord
  trivial

open scoped Classical in
-- TIE 2 : and that count row is exactly what `defectCoveringBridge` produces, read at
-- `σ := ρ`, `ζ := ζ'`, `θ := θ ρ`, `𝕎 := t`.  Nothing is reshaped between the two.
example {ιU ιV ιM κ₀ : Type*} {ρ : NNReal} {q A ρa ρm θ₀ : ℝ}
    (Tb U : Finset ιU) (V V0 : Finset ιV) (ϖ : ιU → ιV)
    (Tm : Finset ιM) (anc : ιU → ιM) (t : Finset κ₀) (chg : ιM → κ₀)
    (Afib A₁ D : ℕ)
    (hUsub : U ⊆ Tb)
    (hret : θ₀ * (Tb.card : ℝ) ≤ (U.card : ℝ))
    (hϖmaps : ∀ u ∈ U, ϖ u ∈ V)
    (hϖsurj : ∀ v ∈ V, ∃ u ∈ U, ϖ u = v)
    (hϖfib : ∀ v ∈ V, (U.filter (fun u => ϖ u = v)).card ≤ Afib)
    (hAfib : (Afib : ℝ) ≤ 5000 ^ 6 * A)
    (hV0 : V0 ⊆ V)
    (hV0card : θ ρ * (V.card : ℝ) ≤ (V0.card : ℝ))
    (hancmaps : ∀ u ∈ Tb, anc u ∈ Tm)
    (hDlo : ∀ x ∈ Tm, D ≤ (Tb.filter (fun u => anc u = x)).card)
    (hDhi : ∀ x ∈ Tm, (Tb.filter (fun u => anc u = x)).card ≤ 2 * D)
    (hchg : ∀ x ∈ (U.filter (fun u => ϖ u ∈ V0)).image anc, chg x ∈ t)
    (hA₁fib : ∀ w ∈ t,
      (((U.filter (fun u => ϖ u ∈ V0)).image anc).filter (fun x => chg x = w)).card ≤ A₁)
    (hfloor : (ρa / ρm) ^ (2 + 4 * ζ') ≤ (Tm.card : ℝ))
    (hgrid : q / (56 * (ρ : ℝ)) ≤ ρa / ρm)
    (htest : (ρ : ℝ) ^ (2 * ζ') ≤ θ₀ * q ^ (3 : ℝ) / (10 ^ 30 * A * A₁))
    (hD0 : 0 < D) (hAfib0 : 0 < Afib) (hA₁0 : 0 < A₁)
    (hθ0 : 0 < θ ρ) (hθ₀0 : 0 < θ₀)
    (hρ0 : (0 : ℝ) < (ρ : ℝ)) (hζ0 : 0 < ζ') (hζ : ζ' ≤ 1 / 4)
    (hq0 : 0 < q) (hq1 : q ≤ 1) (hA1 : 1 ≤ A) : True := by
  have _row : θ ρ * (ρ : ℝ) ^ (-2 - 2 * ζ') ≤ (t.card : ℝ) :=
    Kakeya.ML2Core.defectCoveringBridge Tb U V V0 ϖ Tm anc t chg Afib A₁ D hUsub hret
      hϖmaps hϖsurj hϖfib hAfib hV0 hV0card hancmaps hDlo hDhi hchg hA₁fib hfloor hgrid htest
      hD0 hAfib0 hA₁0
      hθ0 hθ₀0 hρ0 hζ0 hζ hq0 hq1 hA1
  trivial

end Ties

end

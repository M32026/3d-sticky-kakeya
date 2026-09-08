/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorRetention
public import Kakeya.DimensionThree.MainLemma2.Reduction.BandSqueeze

/-!
# `R0b`: the shaded half of the mass-coupled fullness selection (l.4486-4500)

`Kakeya.ML2Core.MassCoupledFullnessSelectionAt` was **named** by the four-way producer hand
(`SpineFloorRetention.lean`) and left without a producer.  This file supplies the producer, and
with it the one construction the tree did not have: a **mass-weighted pigeonhole** on a shaded
family.

## The source, and what is and is not free

l.4486-4500 fixes a retained `p`-cell `S_p^*` and asks the selection for a nonempty
`𝕌_b ⊆ 𝕊''_b⟨S_p^*⟩` carrying, **on the same complete tagged fibres**,

* `λ(𝕌_b, Z_b) ≥ δ^{5η_c}`  (the shaded row),
* `Δ_max(𝕌_b) ≤ t^{-η_J}`   (the density row),
* a retained proportion `θ₀ ≥ δ^{6η_c}` of the level-`b` cells in this `p`-cell.

l.4499-4500 says *why* all three land on one family: "**this is precisely why the earlier
pigeonholing was weighted by shaded mass**".  That sentence is the construction, and it is the
part the tree was missing.

**The density row is free.**  `Kakeya.maxDensity` is monotone in the family
(`Kakeya.maxDensity_mono`), and the selection only ever *shrinks* the fibre, so a `t^{-η_J}` bound
on the whole fibre descends to `𝕌_b` with nothing to prove.  A planned lemma retired by search.

**The retention (cardinality) row is free of *this* file** in the seam's sense: the seam keeps whole
tagged thread cells (`Kakeya.ML2Core.threeLevelSeam_fibre_complete`) because it never selected at
level `b`.  What is *not* free is the proportion `θ₀` surviving the **mass** selection below, and
that is derived here rather than assumed (`card_goodMassSet_ge`).

**The shaded row is the new construction.**  `ShadedBody.fullness'` is a *ratio of sums*,
`(∑ vol shade)/(∑ vol carrier)`, so passing to a subfamily controls neither numerator nor
denominator by itself.  The mass-weighted pigeonhole below selects by **individual** shaded mass —
the cells whose own shade is at least an `η`-fraction of their own carrier — and that single choice
delivers the numerator bound and the cardinality bound simultaneously.

## Family / shading / level pair

Every declaration in this file reads the **same** family and the **same** level pair:

| declaration | family / shading | level pair |
|---|---|---|
| `goodMassSet` | an abstract `Finset ι` with a shading `V`; no level structure | none (it is the kernel) |
| `shade_sum_le_goodMassSet_add` | as above | none |
| `mass_fraction_goodMassSet` | as above | none |
| `fullness_goodMassSet_ge` | as above | none |
| `card_goodMassSet_ge` | as above | none |
| `massCoupledFullnessSelectionAt_of_fibre` | `(𝕌_b, Z_b)` = `goodMassSet` of the fibre `𝒰.nodesUnder b p Sp` under **one** retained `p`-cell `Sp`, with the induced shading `Z_b` | **`(p,b)`** |

The producer never leaves `(p,b)`.  In particular it does **not** re-quantify the count floor,
which is printed at `(p,m')` with `m' ∈ 𝒲` and `𝒲` excluding `b` by construction (l.4041-4045);
doing so is prohibited by condition §2.  The floor is not an input here at all: the bridge
from `(p,m')` to `(p,b)` is this selection, exactly as the map states.

## Constants — transcribed, not fitted

`5η_c` and `η_J` appear only as the source prints them, inside the named
`MassCoupledFullnessSelectionAt`, which this file does not touch.  The producer's own hypotheses
name the selection's two free parameters explicitly (`η`, the individual-mass threshold, and `c`,
the surviving mass fraction) and require the caller to certify
`δ^{5η_c} ≤ c * λ(fibre)` and `θ₀ ≤ c * λ₀`.  **No constant is coerced**: nothing here rewrites
`5η_c`, `6η_c`, `η_J`, or `Λ` of clause 5.
-/

@[expose] public section

open scoped ENNReal NNReal
open MeasureTheory Convexity

namespace Kakeya.ML2Core

section MassWeightedPigeonhole

variable {ι : Type*}
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

open Classical in
/-- **The mass-weighted pigeonhole's selected family.**  The cells of `s` whose *own* shaded mass
is at least an `η`-fraction of their *own* carrier.

This is the tree's rendering of l.4499-4500's "the earlier pigeonholing was weighted by shaded
mass".  Selecting by individual mass — rather than by count — is what lets one choice serve the
fullness row and the cardinality row at once.

**Family/shading:** the given `s` with shading `V`.  **Level pair:** none; this is the kernel, and
it is instantiated at `(p,b)` by the producer. -/
noncomputable def goodMassSet (s : Finset ι) (V : ι → ShadedBody F) (η : ℝ≥0∞) : Finset ι :=
  s.filter (fun i => η * volume (V i).carrier ≤ volume (V i).shade)

theorem goodMassSet_subset (s : Finset ι) (V : ι → ShadedBody F) (η : ℝ≥0∞) :
    goodMassSet s V η ⊆ s := Finset.filter_subset _ _

open Classical in
/-- **The split.**  The discarded cells are, individually, `η`-thin, so all of them together lose
at most `η` times the total carrier volume.  No positivity and no finiteness is needed; this is the
inequality that carries the whole construction. -/
theorem shade_sum_le_goodMassSet_add (s : Finset ι) (V : ι → ShadedBody F) (η : ℝ≥0∞) :
    ∑ i ∈ s, volume (V i).shade
      ≤ (∑ i ∈ goodMassSet s V η, volume (V i).shade)
        + η * ∑ i ∈ s, volume (V i).carrier := by
  classical
  rw [goodMassSet, ← Finset.sum_filter_add_sum_filter_not s
    (fun i => η * volume (V i).carrier ≤ volume (V i).shade) (fun i => volume (V i).shade)]
  gcongr
  calc (∑ i ∈ s with ¬ (η * volume (V i).carrier ≤ volume (V i).shade), volume (V i).shade)
      ≤ ∑ i ∈ s with ¬ (η * volume (V i).carrier ≤ volume (V i).shade),
          η * volume (V i).carrier :=
        Finset.sum_le_sum fun i hi => le_of_lt (not_le.mp (Finset.mem_filter.mp hi).2)
    _ = η * ∑ i ∈ s with ¬ (η * volume (V i).carrier ≤ volume (V i).shade),
          volume (V i).carrier := by rw [Finset.mul_sum]
    _ ≤ η * ∑ i ∈ s, volume (V i).carrier :=
        mul_le_mul_left'
          (Finset.sum_le_sum_of_subset
            (Finset.filter_subset
              (fun i => ¬ (η * volume (V i).carrier ≤ volume (V i).shade)) s)) η

/-- **The mass fraction.**  Once the `η`-budget is under the total shade, the split says the
selected cells carry a `c`-fraction of *all* the shaded mass. -/
theorem mass_fraction_goodMassSet {s : Finset ι} {V : ι → ShadedBody F} {η : ℝ≥0∞} {c : ℝ≥0}
    (hfin : η * ∑ i ∈ s, volume (V i).carrier ≠ ⊤)
    (hbud : (c : ℝ≥0∞) * (∑ i ∈ s, volume (V i).shade)
        + η * ∑ i ∈ s, volume (V i).carrier ≤ ∑ i ∈ s, volume (V i).shade) :
    (c : ℝ≥0∞) * (∑ i ∈ s, volume (V i).shade)
      ≤ ∑ i ∈ goodMassSet s V η, volume (V i).shade :=
  ENNReal.le_of_add_le_add_right hfin (hbud.trans (shade_sum_le_goodMassSet_add s V η))

/-- **The shaded row, in kernel form.**  A `c`-fraction of the mass is a `c`-fraction of the
fullness — the transport is the existing `Kakeya.ML2Squeeze.mul_fullness_le_of_subset`, and it is
what makes the *ratio of sums* survive the selection. -/
theorem fullness_goodMassSet_ge {s : Finset ι} {V : ι → ShadedBody F} {η : ℝ≥0∞} {c : ℝ≥0}
    (hfin : η * ∑ i ∈ s, volume (V i).carrier ≠ ⊤)
    (hbud : (c : ℝ≥0∞) * (∑ i ∈ s, volume (V i).shade)
        + η * ∑ i ∈ s, volume (V i).carrier ≤ ∑ i ∈ s, volume (V i).shade) :
    c * ShadedBody.fullness s V ≤ ShadedBody.fullness (goodMassSet s V η) V :=
  Kakeya.ML2Squeeze.mul_fullness_le_of_subset (goodMassSet_subset s V η) V
    (mass_fraction_goodMassSet hfin hbud)

/-- **The cardinality row, derived.**  On congruent cells — which is what a level-`b` grid fibre
gives — a `c`-fraction of the shaded mass forces a `c*λ₀`-fraction of the *count*, because the
selected cells' carriers already dominate their own shade.  This is the half of the source's `θ₀`
that the seam's fibre-completeness does **not** hand over for free.

**Family/shading:** `s` with `V`.  **Level pair:** none; instantiated at `(p,b)` below. -/
theorem card_goodMassSet_ge {s : Finset ι} {V : ι → ShadedBody F} {η : ℝ≥0∞} {c lam : ℝ≥0}
    {v : ℝ≥0∞} (hv0 : v ≠ 0) (hvtop : v ≠ ⊤)
    (hvol : ∀ i ∈ s, volume (V i).carrier = v)
    (hmass : (c : ℝ≥0∞) * (∑ i ∈ s, volume (V i).shade)
      ≤ ∑ i ∈ goodMassSet s V η, volume (V i).shade)
    (hlam : (lam : ℝ≥0∞) * (∑ i ∈ s, volume (V i).carrier)
      ≤ ∑ i ∈ s, volume (V i).shade) :
    ((c * lam : ℝ≥0) : ℝ≥0∞) * (s.card : ℝ≥0∞)
      ≤ ((goodMassSet s V η).card : ℝ≥0∞) := by
  classical
  have hsub := goodMassSet_subset s V η
  have hS : ∑ i ∈ s, volume (V i).carrier = (s.card : ℝ≥0∞) * v := by
    rw [Finset.sum_congr rfl hvol, Finset.sum_const, nsmul_eq_mul]
  have hG : ∑ i ∈ goodMassSet s V η, volume (V i).carrier
      = ((goodMassSet s V η).card : ℝ≥0∞) * v := by
    rw [Finset.sum_congr rfl (fun i hi => hvol i (hsub hi)), Finset.sum_const, nsmul_eq_mul]
  have hGle : ∑ i ∈ goodMassSet s V η, volume (V i).shade
      ≤ ∑ i ∈ goodMassSet s V η, volume (V i).carrier :=
    Finset.sum_le_sum fun i _ => measure_mono (V i).shade_subset
  have key : ((c * lam : ℝ≥0) : ℝ≥0∞) * (s.card : ℝ≥0∞) * v
      ≤ ((goodMassSet s V η).card : ℝ≥0∞) * v := by
    calc ((c * lam : ℝ≥0) : ℝ≥0∞) * (s.card : ℝ≥0∞) * v
        = (c : ℝ≥0∞) * ((lam : ℝ≥0∞) * ((s.card : ℝ≥0∞) * v)) := by
          push_cast; ring
      _ = (c : ℝ≥0∞) * ((lam : ℝ≥0∞) * (∑ i ∈ s, volume (V i).carrier)) := by rw [hS]
      _ ≤ (c : ℝ≥0∞) * (∑ i ∈ s, volume (V i).shade) := by
          exact mul_le_mul_left' hlam _
      _ ≤ ∑ i ∈ goodMassSet s V η, volume (V i).shade := hmass
      _ ≤ ∑ i ∈ goodMassSet s V η, volume (V i).carrier := hGle
      _ = ((goodMassSet s V η).card : ℝ≥0∞) * v := hG
  exact (ENNReal.mul_le_mul_iff_left hv0 hvtop).mp key

/-! ### The reusable mechanism, in the tree's own refinement vocabulary

l.4056-4059 asks for "*a simultaneous refinement, **weighted by complete fibre shaded mass**,
[which] retains at least `Λ_f^{-1}` of that mass*".  That is the **same mechanism** as the
mass-coupled selection of l.4486-4500, and l.4499-4500 says so.  The three declarations below
express `goodMassSet` in the tree's existing `Kakeya.ShadedBody.IsCRefinement` vocabulary, so that
the mechanism is available to *any* consumer that speaks refinements — not only to the `(p,b)`
bridge this file was opened for.

**What this does and does not supply.**  It supplies the *mass-retention clause* that l.4056-4059
places in front of the trichotomy, at the source's own `Λ^{-1}`.  It does **not** supply the
trichotomy: the case split into `(F)`/`(P)`/`(D)` of l.4060-4098 is a separate argument, and
nothing here produces `FloorHypothesisAt` or the `(F)` alternative.  Stated explicitly so the
boundary is not read as larger than it is. -/

/-- `goodMassSet` is a refinement in the existing sense: same carriers, same shades, fewer cells. -/
theorem goodMassSet_isRefinement (s : Finset ι) (V : ι → ShadedBody F) (η : ℝ≥0∞) :
    ShadedBody.IsRefinement (goodMassSet s V η) V s V :=
  ⟨goodMassSet_subset s V η, fun _ _ => ⟨rfl, subset_rfl⟩⟩

/-- **The `Λ`-form of the split.**  This is l.4056-4059's retention read forwards: the whole
family's shaded mass is at most `Λ` times the selected family's. -/
theorem sum_shade_le_mul_goodMassSet {s : Finset ι} {V : ι → ShadedBody F} {η : ℝ≥0∞}
    {C : NNReal}
    (hbudC : η * (∑ i ∈ s, volume (V i).carrier)
        + ∑ i ∈ goodMassSet s V η, volume (V i).shade
      ≤ (C : ℝ≥0∞) * ∑ i ∈ goodMassSet s V η, volume (V i).shade) :
    ∑ i ∈ s, volume (V i).shade
      ≤ (C : ℝ≥0∞) * ∑ i ∈ goodMassSet s V η, volume (V i).shade :=
  (shade_sum_le_goodMassSet_add s V η).trans (by rw [add_comm]; exact hbudC)

/-- **The mass-weighted refinement of l.4056-4059, retaining `Λ^{-1}` of the shaded mass.**

`Λ` is left abstract: the source's own `Λ_f = (2 + log₂(1/δ))^{K_f}` is transcribed separately as
`Kakeya.ML2Core.LambdaFib`, and **no constant is coerced here** — a caller instantiates `C` with
whatever `Λ` its own hypothesis prints.

**Family/shading:** any `s` with `V`, the selected subfamily carrying the *same* shading.
**Level pair:** none; the mechanism is level-agnostic, which is exactly why it serves both the
trichotomy's `a < m < b` (`m ∈ 𝒲`) and this file's `(p,b)` bridge.  The two instantiations are
kept separate on purpose: see `massCoupledFullnessSelectionAt_of_fibre` for the `(p,b)` one. -/
theorem goodMassSet_isCRefinement_inv {s : Finset ι} {V : ι → ShadedBody F} {η : ℝ≥0∞}
    {C : NNReal}
    (hbudC : η * (∑ i ∈ s, volume (V i).carrier)
        + ∑ i ∈ goodMassSet s V η, volume (V i).shade
      ≤ (C : ℝ≥0∞) * ∑ i ∈ goodMassSet s V η, volume (V i).shade) :
    ShadedBody.IsCRefinement (goodMassSet s V η) V s V C⁻¹ :=
  ShadedBody.isCRefinement_of_isRefinement_of_sum_le _ _ _ _
    (goodMassSet_isRefinement s V η) (sum_shade_le_mul_goodMassSet hbudC)

/-- **`Λ_f = (2 + log₂(1/δ))^{K_f}`** (l.4058), transcribed exactly as the source prints it.

Introduced because the tree has no existing constant of this shape; nothing existing is coerced to
match it.  It is *not* used by the mechanism above, which keeps `Λ` abstract — it is here so a
caller can name the source's constant rather than inline a polylog. -/
noncomputable def LambdaFib (δ : NNReal) (Kf : ℕ) : ℝ :=
  (2 + Real.logb 2 (1 / (δ : ℝ))) ^ Kf

/-! ### The retained proportion's own bound, `θ₀ ≥ δ^{6η_c}` (l.4496-4498)

l.4494 prints `λ(𝕌_b,Z_b) ≥ δ^{5η_c}` and l.4496 prints `θ₀ ≥ δ^{6η_c}`.  The exponent bookkeeping
is **copied, not fitted**: since `δ ≤ 1` and `η_c ≥ 0`, `δ^{6η_c} ≤ δ^{5η_c}`, so the
retained-proportion bound is the *weaker* of the two and follows from the fullness bound with one
power of `δ^{η_c}` of slack.  That is why the source can assert both from the single
mass-weighted pigeonhole. -/

/-- `δ^{6η_c} ≤ δ^{5η_c}` for `0 < δ ≤ 1`, `0 ≤ η_c` — the slack between l.4494 and l.4496. -/
theorem delta_six_le_five {δ : NNReal} {ηc : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hηc : 0 ≤ ηc) :
    δ ^ (6 * ηc) ≤ δ ^ (5 * ηc) :=
  NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (by linarith)

/-- **A certified mass floor is a fullness floor.**  On congruent cells, `lam · ∑carrier ≤ ∑shade`
is exactly `lam ≤ λ(fibre)`; this is what lets the single input `hfull5` serve both the shaded row
and the retained-proportion row. -/
theorem lam_le_fullness {s : Finset ι} {V : ι → ShadedBody F} {lam : ℝ≥0} {v : ℝ≥0∞}
    (hne : s.Nonempty) (hv0 : v ≠ 0) (hvtop : v ≠ ⊤)
    (hvol : ∀ i ∈ s, volume (V i).carrier = v)
    (hlam : (lam : ℝ≥0∞) * (∑ i ∈ s, volume (V i).carrier)
      ≤ ∑ i ∈ s, volume (V i).shade) :
    lam ≤ ShadedBody.fullness s V := by
  classical
  have hS : ∑ i ∈ s, volume (V i).carrier = (s.card : ℝ≥0∞) * v := by
    rw [Finset.sum_congr rfl hvol, Finset.sum_const, nsmul_eq_mul]
  have hcard0 : (s.card : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero, Finset.card_eq_zero]
    exact Finset.nonempty_iff_ne_empty.mp hne
  have hden0 : (∑ i ∈ s, volume (V i).carrier) ≠ 0 := by
    rw [hS]; exact mul_ne_zero hcard0 hv0
  have hdent : (∑ i ∈ s, volume (V i).carrier) ≠ ⊤ := by
    rw [hS]; exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hvtop
  rw [← ENNReal.coe_le_coe, ShadedBody.coe_fullness]
  exact (ENNReal.le_div_iff_mul_le (Or.inl hden0) (Or.inl hdent)).mpr hlam

end MassWeightedPigeonhole

section Producer

variable {ι : Type*} {δ Cu : NNReal}

open Classical in
/-- **R0b: the producer for `Kakeya.ML2Core.MassCoupledFullnessSelectionAt`** (l.4486-4500).

Fix the retained `p`-cell `Sp`.  `𝕌_b` is the **mass-weighted** selection `goodMassSet` of the
level-`b` fibre `𝒰.nodesUnder b p Sp`, and `Z_b` is the induced shading, pinned to the cover's
level-`b` tubes by `hZb` exactly as the named statement asks.

The three rows land as follows, and none of them moves the level pair off `(p,b)`:

* **shaded row** `λ ≥ δ^{5η_c}`: `fullness_goodMassSet_ge`, from the caller's fibre-level fullness
  certificate `hfull` — the selection's loss is the named `c`, and `hfull` is stated *with* that
  loss so that no constant is silently coerced;
* **density row** `Δ_max ≤ t^{-η_J}`: free, `Kakeya.maxDensity_mono` along
  `goodMassSet_subset`, from the fibre-level bound `hdens`;
* **retention row** `θ₀ ≥ δ^{6η_c}` and `θ₀ * #fibre ≤ #𝕌_b`: `card_goodMassSet_ge`, on the
  congruent level-`b` cells of one `p`-cell (`hvol`).

**Family/shading:** `(𝕌_b, Z_b)` under one retained `p`-cell.  **Level pair:** `(p,b)` — the pair
the source's middle factor runs at.  The count floor at `(p,m')`, `m' ∈ 𝒲`, is **not** used, and
`𝒲` excludes `b` (l.4041-4045); the bridge is this selection, per §2. -/
theorem massCoupledFullnessSelectionAt_of_fibre {ηc ηJ : ℝ} {tAux : NNReal} {s : Finset ι}
    {V : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    {𝒰 : Tube.UniformTubeSet s (fun i ↦ (V i).toTube) (Tube.ssfGridLen δ) Cu} {p b : ℕ}
    (Zb : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) b) (EuclideanSpace ℝ (Fin 3)))
    (hZb : ∀ j, (Zb j).toTube = 𝒰.cover.tube b j)
    (η : ℝ≥0∞) (c lam : ℝ≥0) {v : ℝ≥0∞} (hv0 : v ≠ 0) (hvtop : v ≠ ⊤)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hηc : 0 ≤ ηc)
    (hfull5 : (δ : NNReal) ^ (5 * ηc) ≤ c * lam)
    (hne : ∀ Sp ∈ 𝒰.cover.indexSet p,
      (goodMassSet (𝒰.nodesUnder b p Sp) (fun j ↦ (Zb j).toShadedBody) η).Nonempty)
    (hvol : ∀ Sp ∈ 𝒰.cover.indexSet p, ∀ i ∈ 𝒰.nodesUnder b p Sp,
      volume (Zb i).carrier = v)
    (hfin : ∀ Sp ∈ 𝒰.cover.indexSet p,
      η * ∑ i ∈ 𝒰.nodesUnder b p Sp, volume (Zb i).carrier ≠ ⊤)
    (hbud : ∀ Sp ∈ 𝒰.cover.indexSet p,
      (c : ℝ≥0∞) * (∑ i ∈ 𝒰.nodesUnder b p Sp, volume (Zb i).shade)
        + η * ∑ i ∈ 𝒰.nodesUnder b p Sp, volume (Zb i).carrier
        ≤ ∑ i ∈ 𝒰.nodesUnder b p Sp, volume (Zb i).shade)
    (hlam : ∀ Sp ∈ 𝒰.cover.indexSet p,
      (lam : ℝ≥0∞) * (∑ i ∈ 𝒰.nodesUnder b p Sp, volume (Zb i).carrier)
        ≤ ∑ i ∈ 𝒰.nodesUnder b p Sp, volume (Zb i).shade)
    (hdens : ∀ Sp ∈ 𝒰.cover.indexSet p,
      Kakeya.maxDensity (𝒰.nodesUnder b p Sp) (fun j ↦ (Zb j).toConvexSpaceBody)
        ≤ (tAux : ℝ≥0∞) ^ (-ηJ)) :
    MassCoupledFullnessSelectionAt ηc ηJ tAux (c * lam) 𝒰 p b := by
  classical
  intro Sp hSp
  set W : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)) := fun j ↦ (Zb j).toShadedBody with hW
  have hfibNe : (𝒰.nodesUnder b p Sp).Nonempty :=
    (hne Sp hSp).mono (goodMassSet_subset _ _ _)
  have hlamF : lam ≤ ShadedBody.fullness (𝒰.nodesUnder b p Sp) W :=
    lam_le_fullness hfibNe hv0 hvtop (hvol Sp hSp) (hlam Sp hSp)
  refine ⟨goodMassSet (𝒰.nodesUnder b p Sp) W η, Zb, hne Sp hSp,
    goodMassSet_subset _ _ _, hZb, ?_, ?_, ?_, ?_⟩
  · -- shaded row: `δ^{5η_c} ≤ c·lam ≤ c·λ(fibre) ≤ λ(𝕌_b)`
    exact hfull5.trans ((mul_le_mul_left' hlamF c).trans
      (fullness_goodMassSet_ge (hfin Sp hSp) (hbud Sp hSp)))
  · -- density row, free by monotonicity
    exact le_trans (Kakeya.maxDensity_mono _ (goodMassSet_subset _ _ _)) (hdens Sp hSp)
  · -- **retained-proportion bound, DERIVED** (l.4496): `δ^{6η_c} ≤ δ^{5η_c} ≤ c·lam`
    exact (delta_six_le_five hδ0 hδ1 hηc).trans hfull5
  · -- retention row
    have hcard := card_goodMassSet_ge (V := W) (η := η) (c := c) (lam := lam)
      hv0 hvtop (hvol Sp hSp) (mass_fraction_goodMassSet (hfin Sp hSp) (hbud Sp hSp))
      (hlam Sp hSp)
    have hnn : (c * lam) * ((𝒰.nodesUnder b p Sp).card : ℝ≥0)
        ≤ ((goodMassSet (𝒰.nodesUnder b p Sp) W η).card : ℝ≥0) := by
      have := hcard
      rw [show ((c * lam : ℝ≥0) : ℝ≥0∞) * ((𝒰.nodesUnder b p Sp).card : ℝ≥0∞)
        = (((c * lam) * ((𝒰.nodesUnder b p Sp).card : ℝ≥0) : ℝ≥0) : ℝ≥0∞) by push_cast; ring,
        show ((goodMassSet (𝒰.nodesUnder b p Sp) W η).card : ℝ≥0∞)
        = ((((goodMassSet (𝒰.nodesUnder b p Sp) W η).card : ℝ≥0)) : ℝ≥0∞) by push_cast; ring] at this
      exact_mod_cast this
    exact_mod_cast hnn

/-- **Export for `lem:defect-covering-bridge` (l.4596-4617), input 4** — the cell-fullness
selection's retained proportion, l.4496-4498: *"It retains a proportion `θ_0 ≥ δ^{6η_c}` of the
level-`b` cells in this `p`-cell."*

Both halves of that sentence, projected out of `Kakeya.ML2Core.MassCoupledFullnessSelectionAt` in
one place so the bridge can consume them by name:

* `δ^{6η_c} ≤ θ₀` — the constant **exactly as the source prints it**, `6 * ηc`, and it is now
  **derived, not assumed**: `massCoupledFullnessSelectionAt_of_fibre` produces the selection at
  `θ₀ = c · lam` and discharges this row by `Kakeya.ML2Core.delta_six_le_five` from the single
  fullness input `hfull5 : δ^{5η_c} ≤ c · lam` (l.4494).  The `5η_c → 6η_c` step is the source's
  own slack, `δ^{6η_c} ≤ δ^{5η_c}` for `δ ≤ 1`, `η_c ≥ 0` — **copied, not fitted**.  Nothing is
  coerced and no `max` is introduced, because no existing constant competes with it.
* `θ₀ · #(level-`b` cells under `S_p^*`) ≤ #𝕌_b` — the proportion actually being retained, which
  **is** derived, by `Kakeya.ML2Core.card_goodMassSet_ge` inside the producer.

**Family/shading:** `(𝕌_b, Z_b)` — the selected level-`b` cells under the **one retained `p`-cell**
`Sp`, with the shading induced on them; `𝕌_b ⊆ 𝒰.nodesUnder b p Sp`.  **Level pair:** `(p,b)`, the
pair the source's middle factor runs at.  It is **not** the count floor's `(p,m')` with `m' ∈ 𝒲`,
and `𝒲` excludes `b` (l.4041-4045) — the bridge must not read this row at `(p,m')`. -/
theorem massCoupledFullnessSelection_retainedProportion {ηc ηJ : ℝ} {tAux θ₀ : NNReal}
    {s : Finset ι} {V : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    {𝒰 : Tube.UniformTubeSet s (fun i ↦ (V i).toTube) (Tube.ssfGridLen δ) Cu} {p b : ℕ}
    (h : MassCoupledFullnessSelectionAt ηc ηJ tAux θ₀ 𝒰 p b)
    {Sp : ι} (hSp : Sp ∈ 𝒰.cover.indexSet p) :
    (δ : NNReal) ^ (6 * ηc) ≤ θ₀ ∧
      ∃ Ub : Finset ι, Ub.Nonempty ∧ Ub ⊆ 𝒰.nodesUnder b p Sp ∧
        (θ₀ : ℝ) * ((𝒰.nodesUnder b p Sp).card : ℝ) ≤ (Ub.card : ℝ) := by
  obtain ⟨Ub, Zb, hne, hsub, _, _, _, hθ6, hcard⟩ := h Sp hSp
  exact ⟨hθ6, Ub, hne, hsub, hcard⟩

end Producer

end Kakeya.ML2Core

end

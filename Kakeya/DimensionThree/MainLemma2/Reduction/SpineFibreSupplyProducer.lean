/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFibreSupplyRoute
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorShapeHwinfloor

/-!
# The payload producer: `RefinedSupplyAt` from the tree's own inputs

`the estimate`'s four rows, in one pass, **plus a correctness fix to the two frozen batches**.

## 0. The fix, first: the *universally* quantified calibration is unsatisfiable

`SpineFibreStoppingRun.lean`'s `towerGoodFibre_split_of_fibreTest` and
`SpineFibreSupplyRoute.lean`'s `isKatzTaoAtEveryScale_or_dividingWindow` ask for

  `hcal : ∀ j a c b, E · r(a,b)^{-η_j} ≤ r(c,b)^{-η_{j+1}}`

with **no restriction on `(j,a,c,b)`**.  At `a = 0`, `c = b > 0` the right-hand side is
`r(b,b)^{-η_{j+1}} = 1` while the left is `r(0,b)^{-η_j} = δ^{-(b/L)η_j} > 1` for any positive
rung — so no schedule with `η ≢ 0` satisfies it.  `universal_calibration_fails` compiles that.
Both theorems remain **true**; they are simply vacuous at the schedules the run needs, and B10/B11
stay frozen and unedited.

The split uses the calibration only at `(j,a,c,b)` with `j + 1 ≤ N`, `a + w ≤ c`, `c + w ≤ b`,
`b ≤ L`, which is exactly where the source states it (l.5289-5297: `m` lies in the witness range
`W`, and `J ≤ N`).  `towerGoodFibre_split_of_fibreTest_margin`,
`exists_fibreStoppingRun_margin`, `isKatzTaoAtEveryScale_or_dividingWindow_of_cuts` and
`…_run` are the margin-restricted siblings, and they are the ones a producer can feed.  The
`_of_cuts` form takes the run's **output** rather than its inputs, so the two runs share it.

The same defect, milder, is in `hr : ∀ a b, 1 ≤ rinv a b`: the grid ratio `ρ_a/ρ_b` is `≥ 1` only
for `a ≤ b`.  `sourceBound_mono_at` reads it at one pair, and the engine's `hmono` hypothesis
already carries `a < b`, so nothing else is needed.

## 1. A1's one joint pass — already single, and it costs nothing extra

`exists_shadedRefinement_of_joint_bin` (existing) returns **one** `S'` carrying
`IsShadedRefinementOf` — whose sixth conjunct **is** `IsClassHomogeneousOn` — together with all
three bands of the source's l.4030-4035 qualifier paragraph, from a single mass-weighted pass over
`fourStatRow`'s `2L+4` slots.  So the "two producers, two `S'`" worry of `the estimate` item 1 does
not arise: `exists_refinement_classHomogeneous_levelDensityBand` is an *alternative* entry point,
not a second pass.  `exists_oneJointPass` composes the joint bin with
`levelDensityBand_refinedHierarchy` and returns the refinement **and** the band on
`refinedHierarchy`, on the same `S'`.

**Cost, charged:** none beyond the bin's own `Λ = ((J+1)^{2L+4})^{L+1}`, which is what
`IsShadedRefinementOf` already carries; the four statistics were bundled into one row vector
precisely so that one pass covers them.  The pass spends `2 ≤ Cu`
(`isClassHomogeneousOn_of_classCountBand`), discharged at the site by
`two_le_ssfUniformConst`.  The **only** residue is a uniform `Λf`: the bin index `J` is chosen by
`exists_pow_two_bracket` from `#S`, the total shaded mass and the shade floor, and is not
exported, so `IsShadedRefinementOf.mono_loss` cannot be applied without a bound on it.  That is
why `hpass` below is stated at `Λf` directly; `Kakeya.ML2Core.eventually_hΛf_polylogLoss` is where
the assembly side absorbs it.

## 2. `FloorHypothesisAt`: two of the six rows discharged

`floorHypothesisAt_of_fibreWindow` is `floorHypothesisAt_of_windowLevels` with

* **`hpar`** — `ParentAdmissible 𝒰 η' a a`, from the **existing** `parentAdmissible_self`, at the
  price `Cu ≤ δ^{-2η'}`.  `maxDensity_nodesUnder_self_le_cu` records that the fibre route reaches
  the same bound as a *density* statement (`Δ_max(nodesUnder a a jθ) ≤ Cu · Z_fib(a,a) ≤ Cu`), so
  the two agree and the existing one is used;
* **`hgap`** — `4ρ_c ≤ ρ_p` for `a ≤ p < c ≤ b`, from `gridScale_gap_real`, i.e. from the single
  threshold `4δ^{1/L} ≤ 1`.

`hfill` (`FillAt`) stays a hypothesis: it is the source's own fullness clause (l.4030-4031,
"fullness at least `δ^{3η_f}`"), and `SpineFloorShapeNoFill.lean` compiles configurations where it
**fails**, so it is not derivable.  `hCstar`, `hcap`, `hclose` stay scalar hypotheses.

## 3. `le_window_maxDensity`: the count identity holds, but the direction is wrong

`the estimate` item 3 asked whether `FloorHypothesisAt`'s third conjunct supplies the count that
`window_field_of_card` needs.  **Measured: the quantities match and the implication runs the wrong
way.**  Conjunct 3 is a floor on `#(nodesUnder m' p jp)`, which at the genuine parent `p = a` and
`m' = b` is the same family of counts as `#(nodesUnder b a j)`; but
`floorHypothesisAt_of_windowLevels` **derives** conjunct 3 from `hwin` through
`floor_of_windowLevels_of_fill`, so the count is an *output* of the window, not an input to it.
Feeding `le_window_maxDensity` from it would be circular.  The row therefore stays where B11 left
it: reduced by `window_field_of_card` to a containing body, a per-tube volume floor and one
numerical inequality, and carried in `FibreWindowRows`.

## 4. The scalar rows, discharged from `IsSpine`

`isKatzTaoAtEveryScale_or_dividingWindow_spine` takes the tree's own
`η = spineRung`, `ε_d = spineDiv`, `N = spineCount` and discharges, from
`ML2Spine.spineRung_isSpine`:

| row | source of the discharge |
|---|---|
| `0 < ε_d`, `ε_d ≤ 1` | `IsSpine.div_pos`, `spineDiv_le_one` |
| `ε_d² N = 1` | `IsSpine.div_eq` (`e = 1/√N`) |
| `0 ≤ η_j`, `η` monotone, `η_j ≤ ε_d` | `rung_pos`, `rung_mono`, `rung_le_div` |
| `1 ≤ rinv a b` for `a < b` | `one_le_gridRatio` (grid antitone) |
| the margin rows at `w = ⌈ε_d⌈ε_dL⌉⌉` | `KT.stoppingMargin_pos/le`, `KT.le_mul_stoppingMargin` |
| **`hcal`** | `sourceBound_calibration` from `η_j ≤ (w/L)η_{j+1}` |

`η_j ≤ (w/L)η_{j+1}` is itself `rung_le_sq_mul_succ` (`IsSpine.sep_le` with `β ≤ 1`) followed by
`sq_le_margin_div` (`ε_d² ≤ w/L`).

So the calibration `δ^{-ε²η₁/2} ≥ E` is **proved at `E = 1`**, not assumed.

What is left is source-cited and nothing else: `hGood` = the assumed top-cell estimate
(l.2683-2684), `hcrude` = the assumed cardinality estimate at `d = 4` (l.2679-2681), `hwindow`
(reduced to the count), `hfill` (l.4030-4031), and the four numerical thresholds `h4`
(`4δ^{1/L} ≤ 1`, reduced to one logarithm by `gridScale_one_le_quarter`), `hCstarChain`, `hCuη`,
`hCstarNu`, `hcap`, `hclose`.  All are δ-thresholds or the source's own assumptions; none is a
statement about the geometry that this run was asked to prove.

## End state

`refinedSupplyAt_of_fibreRows` → `refinedFloorSupplyAt_of_fibreRows` →
`floorDataAtTrichotomy_of_fibreRows`, the payload side of `GeometricCoreAt`, with the every-scale
disjunct routed out by `hno` per 

## Family / shading / level pair

| declaration | family / shading | level pair |
|---|---|---|
| `sourceBound_mono_at`, `one_le_gridRatio`, `sourceBound_calibration` | none | `(a,c,b)` |
| `…_split_of_fibreTest_margin`, `exists_fibreStoppingRun_margin` | the tower; no shading | cuts |
| `…_of_cuts`, `…_run`, `…_spine` | as above | the window `(a,b,m)` |
| `exists_oneJointPass` | `S`, shading `Z`, refined to `S'`, same shading | every `(p,c)` |
| `maxDensity_nodesUnder_self_le_cu` | the tower; no shading | `(a,a)` |
| `gridScale_gap_real`, `gridScale_one_le_quarter`, `sq_le_margin_div` | none | none |
| `rung_le_sq_mul_succ` | none | none |
| `floorHypothesisAt_of_fibreWindow`, `FibreWindowRows` | the tower; shading via `W` | `(a,b,m)` |
| `refinedSupplyAt_of_fibreRows` + two corollaries | `v` refined to `S'`; shading `Z` | `(a,b,m)` |

## A1-a

No `GridUniformCore` is named.  No `(F)`-branch interface statement is defined or altered: every
interface object is inhabited through a existing constructor, and `FibreWindowRows` is a new
proof-internal `def` naming the source's own assumed rows.
-/

@[expose] public section

open scoped NNReal ENNReal
open MeasureTheory Tube

namespace Kakeya.ML2Core

section MarginCalibration

universe u

variable {ι : Type u} {δ Cu : NNReal} {s : Finset ι}
  {T : ι → Tube δ (EuclideanSpace ℝ (Fin 3))}


/-- **`sourceBound` monotone in the schedule at ONE pair** — the existing `sourceBound_mono` asks for
`1 ≤ rinv a b` at *every* pair, which the grid ratio `ρ_a/ρ_b` satisfies only for `a ≤ b`. -/
theorem sourceBound_mono_at {rinv : ℕ → ℕ → ℝ} {η : ℕ → ℝ} {a b : ℕ} (hr : 1 ≤ rinv a b)
    (hη : ∀ j j' : ℕ, j ≤ j' → η j ≤ η j') (j j' : ℕ) (hjj' : j ≤ j') :
    sourceBound rinv η j a b ≤ sourceBound rinv η j' a b :=
  ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le hr (hη j j' hjj'))

/-- **The grid ratio is `≥ 1` exactly on ordered pairs.** -/
theorem one_le_gridRatio {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {a b : ℕ} (hab : a ≤ b) :
    (1 : ℝ) ≤ (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
      / (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ) := by
  have hb : (0 : ℝ) < (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ) := by
    exact_mod_cast Tube.gridScale_pos hδ0 _ b
  rw [le_div_iff₀ hb, one_mul]
  exact_mod_cast Tube.gridScale_antitone hδ0 hδ1 _ hab

/-- **The calibration `δ^{-ε²η₁/2} ≥ E`, discharged at `E = 1` from one scalar row on the
schedule.** -/
theorem sourceBound_calibration {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hLpos : 0 < Tube.ssfGridLen δ) {η : ℕ → ℝ} (hη0 : ∀ j : ℕ, 0 ≤ η j) {w : ℕ}
    {N : ℕ} (hstep : ∀ j : ℕ, j + 1 ≤ N → η j ≤ ((w : ℝ) / (Tube.ssfGridLen δ : ℝ)) * η (j + 1))
    {rinv : ℕ → ℕ → ℝ}
    (hrinv : ∀ p c : ℕ, rinv p c = (Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ)
      / (Tube.gridScale δ (Tube.ssfGridLen δ) c : ℝ)) :
    ∀ j a c b : ℕ, j + 1 ≤ N → a + w ≤ c → c + w ≤ b → b ≤ Tube.ssfGridLen δ →
      ENNReal.ofReal (1 : ℝ) * sourceBound rinv η j a b ≤ sourceBound rinv η (j + 1) c b := by
  intro j a c b hjN h1 h2 hbL
  rw [ENNReal.ofReal_one, one_mul, sourceBound, sourceBound, hrinv, hrinv]
  refine ENNReal.ofReal_le_ofReal ?_
  have hu0 : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
  have hu1 : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ1
  have hLR : (0 : ℝ) < (Tube.ssfGridLen δ : ℝ) := by exact_mod_cast hLpos
  have hg : ∀ p q : ℕ, (Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ)
      / (Tube.gridScale δ (Tube.ssfGridLen δ) q : ℝ)
      = (δ : ℝ) ^ (((p : ℝ) - (q : ℝ)) / (Tube.ssfGridLen δ : ℝ)) := by
    intro p q
    rw [Tube.gridScale, Tube.gridScale, NNReal.coe_rpow, NNReal.coe_rpow, ← Real.rpow_sub hu0]
    congr 1
    ring
  rw [hg, hg, ← Real.rpow_mul hu0.le, ← Real.rpow_mul hu0.le]
  refine Real.rpow_le_rpow_of_exponent_ge hu0 hu1 ?_
  have hab : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast (by omega : a ≤ b)
  have hbLR : (b : ℝ) ≤ (Tube.ssfGridLen δ : ℝ) := by exact_mod_cast hbL
  have hcw : (c : ℝ) + (w : ℝ) ≤ (b : ℝ) := by exact_mod_cast h2
  have ha0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg _
  have hwn : (0 : ℝ) ≤ (w : ℝ) := Nat.cast_nonneg _
  have hηj := hη0 j
  have hηj1 := hη0 (j + 1)
  have hkey := hstep j hjN
  -- `(b-a)/L ≤ 1` and `(b-c)/L ≥ w/L`
  have hA : ((b : ℝ) - (a : ℝ)) / (Tube.ssfGridLen δ : ℝ) ≤ 1 := by
    rw [div_le_one hLR]; linarith
  have hB : ((w : ℝ) / (Tube.ssfGridLen δ : ℝ))
      ≤ ((b : ℝ) - (c : ℝ)) / (Tube.ssfGridLen δ : ℝ) := by
    have : (w : ℝ) ≤ (b : ℝ) - (c : ℝ) := by linarith
    gcongr
  have h1' : ((b : ℝ) - (a : ℝ)) / (Tube.ssfGridLen δ : ℝ) * η j ≤ η j := by
    nlinarith
  have h2' : ((w : ℝ) / (Tube.ssfGridLen δ : ℝ)) * η (j + 1)
      ≤ ((b : ℝ) - (c : ℝ)) / (Tube.ssfGridLen δ : ℝ) * η (j + 1) := by
    nlinarith
  have hfin : ((b : ℝ) - (a : ℝ)) / (Tube.ssfGridLen δ : ℝ) * η j
      ≤ ((b : ℝ) - (c : ℝ)) / (Tube.ssfGridLen δ : ℝ) * η (j + 1) := by
    linarith
  have hexpand : ∀ p q : ℕ, ((p : ℝ) - (q : ℝ)) / (Tube.ssfGridLen δ : ℝ)
      = -(((q : ℝ) - (p : ℝ)) / (Tube.ssfGridLen δ : ℝ)) := by
    intro p q; ring
  rw [hexpand a b, hexpand c b]
  nlinarith

open scoped Classical in
/-- **`hsplit` with the calibration read only where the split uses it.** -/
theorem towerGoodFibre_split_of_fibreTest_margin
    {𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu} (hs : s.Nonempty)
    {rinv : ℕ → ℕ → ℝ} {η : ℕ → ℝ} {Efac : ℝ} (hE : 1 ≤ Efac) {w : ℕ}
    {N : ℕ}
    (hcal : ∀ j a c b : ℕ, j + 1 ≤ N → a + w ≤ c → c + w ≤ b → b ≤ Tube.ssfGridLen δ →
      ENNReal.ofReal Efac * sourceBound rinv η j a b ≤ sourceBound rinv η (j + 1) c b)
    {j a b : ℕ} (hjN : j + 1 ≤ N) (hbL : b ≤ Tube.ssfGridLen δ)
    (hold : TowerGoodFibre 𝒰 (sourceBound rinv η) j a b ())
    (htest : FibreTest 𝒰 (sourceBound rinv η) w (j + 1) a b ()) :
    ∃ c : ℕ, a + w ≤ c ∧ c + w ≤ b ∧
      TowerGoodFibre 𝒰 (sourceBound rinv η) (j + 1) a c () ∧
      TowerGoodFibre 𝒰 (sourceBound rinv η) (j + 1) c b () := by
  obtain ⟨c, h1, h2, hac⟩ := htest
  refine ⟨c, h1, h2, hac, ?_⟩
  have hcL : c ≤ Tube.ssfGridLen δ := le_trans (Nat.le_add_right c w) (h2.trans hbL)
  have hE1 : (1 : ENNReal) ≤ ENNReal.ofReal Efac := ENNReal.one_le_ofReal.mpr hE
  calc towerDensityArrayFibre 𝒰 c b
      ≤ towerDensityArrayFibre 𝒰 a b :=
        towerDensityArrayFibre_anti_left 𝒰 hs (le_trans (Nat.le_add_right a w) h1) hcL
    _ ≤ ENNReal.ofReal Efac * towerDensityArrayFibre 𝒰 a b :=
        le_mul_of_one_le_left (by simp) hE1
    _ ≤ ENNReal.ofReal Efac * sourceBound rinv η j a b := mul_le_mul' le_rfl hold
    _ ≤ sourceBound rinv η (j + 1) c b := hcal j a c b hjN h1 h2 hbL

open scoped Classical in
/-- **The stopping run at the margin-restricted calibration.** -/
theorem exists_fibreStoppingRun_margin
    (𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu) (hs : s.Nonempty)
    {rinv : ℕ → ℕ → ℝ} {η : ℕ → ℝ} {Efac : ℝ} (hE : 1 ≤ Efac)
    (hr : ∀ a b : ℕ, a < b → 1 ≤ rinv a b) (hη : ∀ j j' : ℕ, j ≤ j' → η j ≤ η j')
    (N w : ℕ)
    (hcal : ∀ j a c b : ℕ, j + 1 ≤ N → a + w ≤ c → c + w ≤ b → b ≤ Tube.ssfGridLen δ →
      ENNReal.ofReal Efac * sourceBound rinv η j a b ≤ sourceBound rinv η (j + 1) c b)
    (hw : 0 < w) (hwM : w ≤ Tube.ssfGridLen δ)
    (hwN : Tube.ssfGridLen δ ≤ w * N) (Long : ℕ → ℕ → Prop)
    (hGood : towerDensityArrayFibre 𝒰 0 (Tube.ssfGridLen δ)
      ≤ sourceBound rinv η 0 0 (Tube.ssfGridLen δ)) :
    ∃ (S : Finset ℕ) (m : ℕ), m < N ∧ 0 ∈ S ∧ Tube.ssfGridLen δ ∈ S ∧
      S ⊆ Finset.range (Tube.ssfGridLen δ + 1) ∧ S.card = m + 2 ∧
      ∀ a ∈ S, ∀ b ∈ S, a < b → (∀ y ∈ S, ¬(a < y ∧ y < b)) →
        towerDensityArrayFibre 𝒰 a b ≤ sourceBound rinv η m a b ∧
        (¬ Long a b ∨ ∀ c : ℕ, a + w ≤ c → c + w ≤ b →
          sourceBound rinv η (m + 1) a c < towerDensityArrayFibre 𝒰 a c) := by
  classical
  obtain ⟨S, m, hmN, h0, hM, hsub, hcard, hpieces⟩ :=
    exists_fixedTowerCutsFibre 𝒰 (Tube.ssfGridLen δ) N w hw hwM hwN (sourceBound rinv η)
      (FibreTest 𝒰 (sourceBound rinv η) w) Long hGood
      (fun j j' hjj' _ a b hab hg =>
        le_trans hg (sourceBound_mono_at (hr a b hab) hη j j' hjj'))
      (fun j a b hjN _ hbM _ hg htest =>
        towerGoodFibre_split_of_fibreTest_margin hs hE hcal hjN hbM hg htest)
  refine ⟨S, m, hmN, h0, hM, hsub, hcard, fun a ha b hb hab hadj => ?_⟩
  obtain ⟨hgood, halt⟩ := hpieces a ha b hb hab hadj
  refine ⟨hgood, halt.imp id (fun hnt c h1 h2 => ?_)⟩
  by_contra hcon
  exact hnt ⟨c, h1, h2, not_lt.mp hcon⟩

end MarginCalibration

section DichotomyFromCuts

universe u

variable {ι : Type u} {δ Cu : NNReal} {s : Finset ι}
  {T : ι → Tube δ (EuclideanSpace ℝ (Fin 3))}

open scoped Classical in
/-- **The dichotomy, factored through the run's *output*.** -/
theorem isKatzTaoAtEveryScale_or_dividingWindow_of_cuts (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (h4 : 4 * Tube.gridScale δ (Tube.ssfGridLen δ) 1 ≤ 1) (hLpos : 0 < Tube.ssfGridLen δ)
    (𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu) (hs : s.Nonempty)
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)
    {Cstar : ENNReal} {η : ℕ → ℝ} {εd : ℝ} (hεd : 0 ≤ εd) {N w : ℕ}
    {rinv : ℕ → ℕ → ℝ}
    (hrinv : ∀ p c : ℕ, rinv p c = (Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ)
      / (Tube.gridScale δ (Tube.ssfGridLen δ) c : ℝ))
    (hη0 : ∀ j : ℕ, 0 ≤ η j) (hηεd : ∀ j : ℕ, η j ≤ εd)
    (hwmar : w ≤ ⌈εd * ((⌈εd * (Tube.ssfGridLen δ : ℝ)⌉₊ : ℕ) : ℝ)⌉₊)
    {D : ENNReal} (hD1 : 1 ≤ D)
    (hcrude : ∀ p c : ℕ, p ≤ c → c ≤ Tube.ssfGridLen δ →
      towerDensityArrayFibre 𝒰 p c ≤ D * ENNReal.ofReal
        (((Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ)
          / (Tube.gridScale δ (Tube.ssfGridLen δ) c : ℝ)) ^ (4 : ℕ)))
    (hCstarChain : (Cu : ENNReal) * fibreChainConst.{u} ^ (N + 1) ≤ Cstar)
    (hwindow : ∀ a b m : ℕ, ∀ ρ : NNReal,
      (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
          * ((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
            / (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)) ^ εd ≤ (ρ : ℝ) →
      (ρ : ℝ) ≤ (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
          * ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
            / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) ^ εd →
      ∀ j ∈ 𝒰.cover.indexSet a,
        ENNReal.ofReal (((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ) / (ρ : ℝ)) ^ η (m + 1))
          ≤ Cstar * Kakeya.maxDensity (𝒰.nodesUnder b a j)
              (fun j' => ((𝒰.cover.tube b j').rescale ρ).toConvexSpaceBody))
    {Φ : ℕ → ℕ → ENNReal}
    (hband : ∀ p ≤ Tube.ssfGridLen δ, ∀ c ≤ Tube.ssfGridLen δ, ∀ j ∈ 𝒰.cover.indexSet p,
      Φ p c ≤ Kakeya.maxDensity (𝒰.assignFibre c p j)
          (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) ∧
        Kakeya.maxDensity (𝒰.assignFibre c p j)
          (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) ≤ Cstar * Φ p c)
    {S : Finset ℕ} {m : ℕ} (hmN : m < N) (h0 : 0 ∈ S) (hLmem : Tube.ssfGridLen δ ∈ S)
    (hsubr : S ⊆ Finset.range (Tube.ssfGridLen δ + 1)) (hcard : S.card = m + 2)
    (hpieces : ∀ a ∈ S, ∀ b ∈ S, a < b → (∀ y ∈ S, ¬(a < y ∧ y < b)) →
      towerDensityArrayFibre 𝒰 a b ≤ sourceBound rinv η m a b ∧
      (¬ (⌈εd * (Tube.ssfGridLen δ : ℝ)⌉₊ + a ≤ b) ∨ ∀ c : ℕ, a + w ≤ c → c + w ≤ b →
        sourceBound rinv η (m + 1) a c < towerDensityArrayFibre 𝒰 a c)) :
    𝒰.IsKatzTaoAtEveryScale ((Cu : ENNReal) * (fibreChainConst.{u} ^ (N + 2)
        * (D * ENNReal.ofReal ((δ : ℝ) ^ (-(5 * εd))))))
      ∨ ∃ a b m : ℕ, ML2Reduction.IsKatzTaoDividingWindowLevels 𝒰 Cstar η εd N a b m := by
  classical
  have hδ1' : δ ≤ 1 := hδ1.le
  have hSL : ∀ x ∈ S, x ≤ Tube.ssfGridLen δ := by
    intro x hx
    have := Finset.mem_range.mp (hsubr hx)
    omega
  by_cases hex : ∃ a ∈ S, ∃ b ∈ S, a < b ∧ (∀ y ∈ S, ¬(a < y ∧ y < b)) ∧
      ⌈εd * (Tube.ssfGridLen δ : ℝ)⌉₊ + a ≤ b
  · right
    obtain ⟨a, ha, b, hb, hab, hadj, hlong⟩ := hex
    obtain ⟨hgood, halt⟩ := hpieces a ha b hb hab hadj
    have hwit := halt.resolve_left (not_not_intro hlong)
    have hbL : b ≤ Tube.ssfGridLen δ := hSL b hb
    have hceil : εd * (Tube.ssfGridLen δ : ℝ) ≤ (⌈εd * (Tube.ssfGridLen δ : ℝ)⌉₊ : ℝ) :=
      Nat.le_ceil _
    have hbaR : ((⌈εd * (Tube.ssfGridLen δ : ℝ)⌉₊ : ℕ) : ℝ) ≤ (b : ℝ) - (a : ℝ) := by
      have : ((⌈εd * (Tube.ssfGridLen δ : ℝ)⌉₊ : ℕ) : ℝ) + (a : ℝ) ≤ (b : ℝ) := by
        exact_mod_cast hlong
      linarith
    have hwidth : εd * (Tube.ssfGridLen δ : ℝ) + (a : ℝ) ≤ (b : ℝ) := by linarith
    have hwmargin : w ≤ ⌈εd * ((b : ℝ) - (a : ℝ))⌉₊ :=
      le_trans hwmar (Nat.ceil_le_ceil (by nlinarith))
    have hchain := towerDensityArrayFibre_zero_le_of_cuts' hδ0 hδ1' 𝒰 hs hball h0 hSL
      (fun p _ c _ hpc => gridScale_gap_of_step hδ0 hδ1' h4 hpc) hrinv
      (fun x hx y hy hxy hadj' => (hpieces x hx y hy hxy hadj').1) ha
    have hcoarse : (Cu : ENNReal) * towerDensityArrayFibre 𝒰 0 a
        ≤ Cstar * ENNReal.ofReal
            ((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ) ^ (-η m)) := by
      calc (Cu : ENNReal) * towerDensityArrayFibre 𝒰 0 a
          ≤ (Cu : ENNReal) * (fibreChainConst.{u} ^ S.card * sourceBound rinv η m 0 a) :=
            mul_le_mul' le_rfl hchain
        _ = ((Cu : ENNReal) * fibreChainConst.{u} ^ S.card) * sourceBound rinv η m 0 a := by
            ring
        _ ≤ ((Cu : ENNReal) * fibreChainConst.{u} ^ (N + 1)) * sourceBound rinv η m 0 a := by
            refine mul_le_mul' (mul_le_mul' le_rfl ?_) le_rfl
            exact pow_le_pow_right' (a := fibreChainConst.{u}) one_le_fibreChainConst.{u}
              (show S.card ≤ N + 1 by omega)
        _ ≤ Cstar * sourceBound rinv η m 0 a := mul_le_mul' hCstarChain le_rfl
        _ = Cstar * ENNReal.ofReal
              ((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ) ^ (-η m)) := by
            rw [sourceBound_zero_eq hδ0 hrinv]
    exact ⟨a, b, m, isKatzTaoDividingWindowLevels_of_fibreRun_band hδ0 hδ1 𝒰 hs hball
      (le_trans (le_mul_of_one_le_right (by simp) (one_le_pow₀ one_le_fibreChainConst.{u}))
        hCstarChain)
      hrinv hmN hab hbL hwidth hwmargin hgood hwit hcoarse (hwindow a b m) hband⟩
  · left
    have hshort : ∀ a ∈ S, ∀ b ∈ S, a < b → (∀ y ∈ S, ¬(a < y ∧ y < b)) →
        (b : ℝ) - (a : ℝ) ≤ εd * (Tube.ssfGridLen δ : ℝ) := by
      intro a ha b hb hab hadj
      have hlt : b < ⌈εd * (Tube.ssfGridLen δ : ℝ)⌉₊ + a := by
        by_contra hcon
        exact hex ⟨a, ha, b, hb, hab, hadj, by omega⟩
      have h1 : (b : ℝ) + 1 ≤ ((⌈εd * (Tube.ssfGridLen δ : ℝ)⌉₊ : ℕ) : ℝ) + (a : ℝ) := by
        exact_mod_cast hlt
      have h2 : ((⌈εd * (Tube.ssfGridLen δ : ℝ)⌉₊ : ℕ) : ℝ)
          < εd * (Tube.ssfGridLen δ : ℝ) + 1 := Nat.ceil_lt_add_one (by positivity)
      linarith
    refine Tube.UniformTubeSet.IsKatzTaoAtEveryScale.mono
      (isKatzTaoAtEveryScale_of_allShort hδ0 hδ1' h4 hLpos 𝒰 hs hball h0 hSL hLmem hrinv
        (hη0 m) hεd (fun x hx y hy hxy hadj' => (hpieces x hx y hy hxy hadj').1) hshort hD1
        hcrude) ?_
    refine mul_le_mul' le_rfl (mul_le_mul' ?_ (mul_le_mul' le_rfl ?_))
    · exact pow_le_pow_right' (a := fibreChainConst.{u}) one_le_fibreChainConst.{u}
        (show S.card + 1 ≤ N + 2 by omega)
    · refine ENNReal.ofReal_le_ofReal ?_
      have hu0 : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
      have hu1 : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ1'
      refine Real.rpow_le_rpow_of_exponent_ge hu0 hu1 ?_
      have := hηεd m
      linarith

open scoped Classical in
/-- **The dichotomy at the source's own margin `w = ⌈ε⌈εM⌉⌉`**, with `hw`, `hwM`, `hwN` and
`hwmar` all discharged from `0 < ε_d ≤ 1` and `ε_d²N = 1`. -/
theorem isKatzTaoAtEveryScale_or_dividingWindow_run (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (h4 : 4 * Tube.gridScale δ (Tube.ssfGridLen δ) 1 ≤ 1) (hLpos : 0 < Tube.ssfGridLen δ)
    (𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu) (hs : s.Nonempty)
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)
    {Cstar : ENNReal} {η : ℕ → ℝ} {εd : ℝ} (hεd0 : 0 < εd) (hεd1 : εd ≤ 1) {N : ℕ}
    (hεdN : εd ^ 2 * (N : ℝ) = 1)
    {rinv : ℕ → ℕ → ℝ}
    (hrinv : ∀ p c : ℕ, rinv p c = (Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ)
      / (Tube.gridScale δ (Tube.ssfGridLen δ) c : ℝ))
    (hr : ∀ a b : ℕ, a < b → 1 ≤ rinv a b) (hηmono : ∀ j j' : ℕ, j ≤ j' → η j ≤ η j')
    (hη0 : ∀ j : ℕ, 0 ≤ η j) (hηεd : ∀ j : ℕ, η j ≤ εd)
    {Efac : ℝ} (hE : 1 ≤ Efac)
    (hcal : ∀ j a c b : ℕ, j + 1 ≤ N →
      a + ⌈εd * ((⌈εd * (Tube.ssfGridLen δ : ℝ)⌉₊ : ℕ) : ℝ)⌉₊ ≤ c →
      c + ⌈εd * ((⌈εd * (Tube.ssfGridLen δ : ℝ)⌉₊ : ℕ) : ℝ)⌉₊ ≤ b → b ≤ Tube.ssfGridLen δ →
      ENNReal.ofReal Efac * sourceBound rinv η j a b ≤ sourceBound rinv η (j + 1) c b)
    (hGood : towerDensityArrayFibre 𝒰 0 (Tube.ssfGridLen δ)
      ≤ sourceBound rinv η 0 0 (Tube.ssfGridLen δ))
    {D : ENNReal} (hD1 : 1 ≤ D)
    (hcrude : ∀ p c : ℕ, p ≤ c → c ≤ Tube.ssfGridLen δ →
      towerDensityArrayFibre 𝒰 p c ≤ D * ENNReal.ofReal
        (((Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ)
          / (Tube.gridScale δ (Tube.ssfGridLen δ) c : ℝ)) ^ (4 : ℕ)))
    (hCstarChain : (Cu : ENNReal) * fibreChainConst.{u} ^ (N + 1) ≤ Cstar)
    (hwindow : ∀ a b m : ℕ, ∀ ρ : NNReal,
      (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
          * ((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
            / (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)) ^ εd ≤ (ρ : ℝ) →
      (ρ : ℝ) ≤ (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
          * ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
            / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) ^ εd →
      ∀ j ∈ 𝒰.cover.indexSet a,
        ENNReal.ofReal (((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ) / (ρ : ℝ)) ^ η (m + 1))
          ≤ Cstar * Kakeya.maxDensity (𝒰.nodesUnder b a j)
              (fun j' => ((𝒰.cover.tube b j').rescale ρ).toConvexSpaceBody))
    {Φ : ℕ → ℕ → ENNReal}
    (hband : ∀ p ≤ Tube.ssfGridLen δ, ∀ c ≤ Tube.ssfGridLen δ, ∀ j ∈ 𝒰.cover.indexSet p,
      Φ p c ≤ Kakeya.maxDensity (𝒰.assignFibre c p j)
          (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) ∧
        Kakeya.maxDensity (𝒰.assignFibre c p j)
          (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) ≤ Cstar * Φ p c) :
    𝒰.IsKatzTaoAtEveryScale ((Cu : ENNReal) * (fibreChainConst.{u} ^ (N + 2)
        * (D * ENNReal.ofReal ((δ : ℝ) ^ (-(5 * εd))))))
      ∨ ∃ a b m : ℕ, ML2Reduction.IsKatzTaoDividingWindowLevels 𝒰 Cstar η εd N a b m := by
  classical
  obtain ⟨S, m, hmN, h0, hLmem, hsubr, hcard, hpieces⟩ :=
    exists_fibreStoppingRun_margin 𝒰 hs hE hr hηmono N
      ⌈εd * ((⌈εd * (Tube.ssfGridLen δ : ℝ)⌉₊ : ℕ) : ℝ)⌉₊ hcal
      (Kakeya.MultiScaleFac.KT.stoppingMargin_pos hεd0 hLpos)
      (Kakeya.MultiScaleFac.KT.stoppingMargin_le hεd0 hεd1 _)
      (Kakeya.MultiScaleFac.KT.le_mul_stoppingMargin hεd0 hεdN _)
      (fun a b => ⌈εd * (Tube.ssfGridLen δ : ℝ)⌉₊ + a ≤ b) hGood
  exact isKatzTaoAtEveryScale_or_dividingWindow_of_cuts hδ0 hδ1 h4 hLpos 𝒰 hs hball
    hεd0.le hrinv hη0 hηεd le_rfl hD1 hcrude hCstarChain hwindow hband hmN h0 hLmem hsubr
    hcard hpieces

end DichotomyFromCuts

section OneJointPass

variable {ι : Type*} {δ Cu : NNReal}

open scoped Classical in
/-- **A1's one joint pass: a single `S'` carrying the refinement AND the band.** -/
theorem exists_oneJointPass (hδ : 0 < δ) (hCu : 2 ≤ Cu)
    {S : Finset ι} (Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
    (𝒱 : Tube.UniformTubeSet S (fun i => (Z i).toTube) (Tube.ssfGridLen δ) Cu)
    (hS : S.Nonempty) {mfl : ENNReal} (hm0 : mfl ≠ 0)
    (hm : ∀ i ∈ S, mfl ≤ MeasureTheory.volume (Z i).shade)
    {Cstar : ENNReal} (hCstar : 2 ≤ Cstar) :
    ∃ (S' : Finset ι) (J : ℕ) (hS' : S' ⊆ S) (hhom : IsClassHomogeneousOn 𝒱 S'),
      IsShadedRefinementOf 𝒱 ((((J + 1 : ENNReal)) ^ (2 * Tube.ssfGridLen δ + 4))
          ^ (Tube.ssfGridLen δ + 1)) S Z S' Z ∧
      ∃ Φ : ℕ → ℕ → ENNReal, ∀ p ≤ Tube.ssfGridLen δ, ∀ c ≤ Tube.ssfGridLen δ,
        ∀ j ∈ (refinedHierarchy 𝒱 hS' hhom rfl).cover.indexSet p,
        Φ p c ≤ Kakeya.maxDensity ((refinedHierarchy 𝒱 hS' hhom rfl).assignFibre c p j)
            (fun j' => ((refinedHierarchy 𝒱 hS' hhom rfl).cover.tube c j').toConvexSpaceBody) ∧
          Kakeya.maxDensity ((refinedHierarchy 𝒱 hS' hhom rfl).assignFibre c p j)
            (fun j' => ((refinedHierarchy 𝒱 hS' hhom rfl).cover.tube c j').toConvexSpaceBody)
            ≤ Cstar * Φ p c := by
  classical
  obtain ⟨S', J, hS', -, href, ⟨Φ, hΦ⟩, -, -⟩ :=
    exists_shadedRefinement_of_joint_bin hδ hCu Z 𝒱 hS hm0 hm
  exact ⟨S', J, hS', href.2.2.2.2.2, href,
    levelDensityBand_refinedHierarchy 𝒱 hS' href.2.2.2.2.2 rfl hCstar hΦ⟩

end OneJointPass

section FloorRows

universe u

variable {ι : Type u} {δ Cu : NNReal} {s : Finset ι}
  {T : ι → Tube δ (EuclideanSpace ℝ (Fin 3))}

/-- **Control: `ParentAdmissible` at `(a,a)` is existing, and the fibre route re-proves it at the
same price.**  `Kakeya.ML2Core.parentAdmissible_self` (`SpineFloorParent.lean:120`) gets it from
`card_nodesUnder_self_le`; the bounded-overlap comparison of `SpineFibreStoppingRun.lean` gets the
same bound as a *density* statement, `Δ_max(nodesUnder a a jθ) ≤ Cu · Z_fib(a,a) ≤ Cu`.  Recorded
so that the two routes are known to agree and the existing one is used. -/
theorem maxDensity_nodesUnder_self_le_cu
    (𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu) (hs : s.Nonempty)
    {a : ℕ} (ha : a ≤ Tube.ssfGridLen δ) {jθ : ι} (hjθ : jθ ∈ 𝒰.cover.indexSet a) :
    Kakeya.maxDensity (𝒰.nodesUnder a a jθ)
      (fun j => (𝒰.cover.tube a j).toConvexSpaceBody) ≤ (Cu : ENNReal) := by
  refine le_trans (maxDensity_nodesUnder_le_mul_towerDensityArrayFibre 𝒰 hs ha ha hjθ) ?_
  refine le_trans (mul_le_mul' le_rfl (towerDensityArrayFibre_self_le_one 𝒰 a)) ?_
  rw [mul_one]

/-- **The `hgap` row, in the real-valued shape `floorHypothesisAt_of_windowLevels` asks for.** -/
theorem gridScale_gap_real {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (h4 : 4 * Tube.gridScale δ (Tube.ssfGridLen δ) 1 ≤ 1) {p c : ℕ} (hpc : p < c) :
    4 * (Tube.gridScale δ (Tube.ssfGridLen δ) c : ℝ)
      ≤ (Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ) := by
  have h := gridScale_gap_of_step hδ0 hδ1 h4 hpc
  have := NNReal.coe_le_coe.mpr h
  push_cast at this
  linarith

/-- **The scale threshold `4δ^{1/L} ≤ 1`, reduced to one logarithmic inequality.** -/
theorem gridScale_one_le_quarter {δ : NNReal} (hδ0 : 0 < δ)
    (hLpos : 0 < Tube.ssfGridLen δ)
    (hlog : (Tube.ssfGridLen δ : ℝ) * Real.log 4 ≤ -Real.log (δ : ℝ)) :
    4 * Tube.gridScale δ (Tube.ssfGridLen δ) 1 ≤ 1 := by
  have hδr0 : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
  have hLR : (0 : ℝ) < (Tube.ssfGridLen δ : ℝ) := by exact_mod_cast hLpos
  rw [← NNReal.coe_le_coe]
  push_cast
  rw [Tube.gridScale, NNReal.coe_rpow, Nat.cast_one]
  have hexp : (δ : ℝ) ^ ((1 : ℝ) / (Tube.ssfGridLen δ : ℝ))
      = Real.exp (Real.log (δ : ℝ) / (Tube.ssfGridLen δ : ℝ)) := by
    rw [Real.rpow_def_of_pos hδr0]
    ring_nf
  have hquarter : Real.exp (Real.log (δ : ℝ) / (Tube.ssfGridLen δ : ℝ))
      ≤ Real.exp (-Real.log 4) := by
    refine Real.exp_le_exp.mpr ?_
    rw [div_le_iff₀ hLR]
    nlinarith [hlog]
  have h4pos : (0 : ℝ) < 4 := by norm_num
  have hexp4 : Real.exp (-Real.log 4) = 1 / 4 := by
    rw [Real.exp_neg, Real.exp_log h4pos]
    norm_num
  rw [hexp]
  rw [hexp4] at hquarter
  linarith

end FloorRows

section FloorWiring

variable {ι : Type*} {δ Cu : NNReal} {u : Finset ι}
  {V : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}

open scoped Classical in
/-- **`FloorHypothesisAt` with the `hpar` and `hgap` rows discharged.** -/
theorem floorHypothesisAt_of_fibreWindow {β ϖ ε₁ η' κ : ℝ} {gain dens : ℝ → ℝ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    (hη' : 0 < η') (hκ : 0 < κ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (h4 : 4 * Tube.gridScale δ (Tube.ssfGridLen δ) 1 ≤ 1)
    (𝒰 : Tube.UniformTubeSet u (fun i ↦ (V i).toTube) (Tube.ssfGridLen δ) Cu)
    (hs : u.Nonempty)
    (hball : ∀ i ∈ u, ((V i).toTube).carrier
      ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (hCuη : (Cu : ENNReal) ≤ (δ : ENNReal) ^ (-(2 * η')))
    {Cstar : ENNReal} {a b m : ℕ}
    (hwin : ML2Reduction.IsKatzTaoDividingWindowLevels 𝒰 Cstar
      (ML2Spine.spineRung β ϖ ε₁ gain dens) (ML2Spine.spineDiv ϖ ε₁)
      (ML2Spine.spineCount ϖ ε₁) a b m)
    (hCstar : Cstar ≤ (δ : ENNReal) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens / 20)))
    (hcap : η' ≤ ML2Spine.spineDiv ϖ ε₁ ^ 2
      * ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1) / 64)
    (hfill : ∀ jθ ∈ 𝒰.cover.indexSet a, ∀ jp ∈ 𝒰.nodesUnder a a jθ, ∀ m' : ℕ, a < m' → m' ≤ b →
      FillAt 𝒰 κ a m' jp)
    (hclose : ∀ m' : ℕ, a + ⌈ML2Spine.spineDiv ϖ ε₁ * ((b : ℝ) - (a : ℝ))⌉₊ ≤ m' → a < m' →
      m' ≤ b →
      ENNReal.ofReal (((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
              / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ))
            ^ (4 * (ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1) / 16)))
          * (Cstar ^ 2 * ENNReal.ofReal (twoScaleConst.{u_1, 0} (EuclideanSpace ℝ (Fin 3)) ^ 2)
              * (Cu : ENNReal) * (δ : ENNReal) ^ (-(2 * η'))
              * ((Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : NNReal)
                : ENNReal))
        ≤ ENNReal.ofReal (((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
              / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ))
            ^ ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1))
          * ENNReal.ofReal κ
          * ((Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : NNReal)
            : ENNReal)) :
    FloorHypothesisAt β ϖ ε₁ gain dens η' 𝒰 a b m := by
  have haL : a ≤ Tube.ssfGridLen δ :=
    le_trans hwin.toIsKatzTaoDividingWindow.coarse_lt_fine.le
      hwin.toIsKatzTaoDividingWindow.fine_le_gridLen
  exact floorHypothesisAt_of_windowLevels hβ0 hβ1 hϖ hε₁ hgain hdens hη' hκ hδ0 hδ1 𝒰 hs hball
    hwin hCstar hcap (fun p c _ hpc _ => gridScale_gap_real hδ0 hδ1.le h4 hpc)
    (parentAdmissible_self 𝒰 haL hs hCuη) hfill hclose

end FloorWiring

section SpineScalars

/-- **`ε² ≤ w/M` for the source's own margin `w = ⌈ε⌈εM⌉⌉`.** -/
theorem sq_le_margin_div {ε : ℝ} (hε : 0 < ε) {M : ℕ} (hM : 0 < M) :
    ε ^ 2 ≤ ((⌈ε * ((⌈ε * (M : ℝ)⌉₊ : ℕ) : ℝ)⌉₊ : ℕ) : ℝ) / (M : ℝ) := by
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  rw [le_div_iff₀ hMR]
  have h1 : ε * (M : ℝ) ≤ ((⌈ε * (M : ℝ)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have h2 : ε * ((⌈ε * (M : ℝ)⌉₊ : ℕ) : ℝ)
      ≤ ((⌈ε * ((⌈ε * (M : ℝ)⌉₊ : ℕ) : ℝ)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  nlinarith

/-- **The schedule's calibration row, read off `IsSpine`.**  `sep_le` is
`12 η_k/(eβ) ≤ e η_{k+1}/4`, i.e. `η_k ≤ e²β η_{k+1}/48`; with `β ≤ 1` that is below
`e² η_{k+1}`. -/
theorem rung_le_sq_mul_succ {β ϖ ε₁ ε₂ e : ℝ} {gain dens : ℝ → ℝ} {N : ℕ} {η : ℕ → ℝ}
    (hsp : ML2Spine.IsSpine β ϖ ε₁ gain dens ε₂ e N η) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    {k : ℕ} (hk : k < N) : η k ≤ e ^ 2 * η (k + 1) := by
  have he : 0 < e := hsp.div_pos
  have hηk1 : 0 < η (k + 1) := hsp.rung_pos (k + 1)
  have hsep := hsp.sep_le k hk
  have hkey : 12 * η k / (e * β) ≤ e * η (k + 1) / 4 := hsep
  have heβ : 0 < e * β := mul_pos he hβ0
  rw [div_le_iff₀ heβ] at hkey
  nlinarith [hsp.rung_pos k]

end SpineScalars

section SpineDichotomy

universe u

variable {ι : Type u} {δ Cu : NNReal} {s : Finset ι}
  {T : ι → Tube δ (EuclideanSpace ℝ (Fin 3))}

open scoped Classical in
/-- **The dichotomy at the tree's own parameters**, with every schedule row discharged from
`Kakeya.ML2Spine.spineRung_isSpine`. -/
theorem isKatzTaoAtEveryScale_or_dividingWindow_spine {β ϖ ε₁ : ℝ} {gain dens : ℝ → ℝ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (h4 : 4 * Tube.gridScale δ (Tube.ssfGridLen δ) 1 ≤ 1) (hLpos : 0 < Tube.ssfGridLen δ)
    (𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu) (hs : s.Nonempty)
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)
    {Cstar : ENNReal}
    (hCstarChain : (Cu : ENNReal)
      * fibreChainConst.{u} ^ (ML2Spine.spineCount ϖ ε₁ + 1) ≤ Cstar)
    (hGood : towerDensityArrayFibre 𝒰 0 (Tube.ssfGridLen δ)
      ≤ ENNReal.ofReal (((Tube.gridScale δ (Tube.ssfGridLen δ) 0 : ℝ)
          / (Tube.gridScale δ (Tube.ssfGridLen δ) (Tube.ssfGridLen δ) : ℝ))
        ^ ML2Spine.spineRung β ϖ ε₁ gain dens 0))
    {D : ENNReal} (hD1 : 1 ≤ D)
    (hcrude : ∀ p c : ℕ, p ≤ c → c ≤ Tube.ssfGridLen δ →
      towerDensityArrayFibre 𝒰 p c ≤ D * ENNReal.ofReal
        (((Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ)
          / (Tube.gridScale δ (Tube.ssfGridLen δ) c : ℝ)) ^ (4 : ℕ)))
    (hwindow : ∀ a b m : ℕ, ∀ ρ : NNReal,
      (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
          * ((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
            / (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)) ^ ML2Spine.spineDiv ϖ ε₁ ≤ (ρ : ℝ) →
      (ρ : ℝ) ≤ (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
          * ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
            / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) ^ ML2Spine.spineDiv ϖ ε₁ →
      ∀ j ∈ 𝒰.cover.indexSet a,
        ENNReal.ofReal (((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ) / (ρ : ℝ))
            ^ ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1))
          ≤ Cstar * Kakeya.maxDensity (𝒰.nodesUnder b a j)
              (fun j' => ((𝒰.cover.tube b j').rescale ρ).toConvexSpaceBody))
    {Φ : ℕ → ℕ → ENNReal}
    (hband : ∀ p ≤ Tube.ssfGridLen δ, ∀ c ≤ Tube.ssfGridLen δ, ∀ j ∈ 𝒰.cover.indexSet p,
      Φ p c ≤ Kakeya.maxDensity (𝒰.assignFibre c p j)
          (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) ∧
        Kakeya.maxDensity (𝒰.assignFibre c p j)
          (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) ≤ Cstar * Φ p c) :
    𝒰.IsKatzTaoAtEveryScale ((Cu : ENNReal)
        * (fibreChainConst.{u} ^ (ML2Spine.spineCount ϖ ε₁ + 2)
          * (D * ENNReal.ofReal ((δ : ℝ) ^ (-(5 * ML2Spine.spineDiv ϖ ε₁))))))
      ∨ ∃ a b m : ℕ, ML2Reduction.IsKatzTaoDividingWindowLevels 𝒰 Cstar
          (ML2Spine.spineRung β ϖ ε₁ gain dens) (ML2Spine.spineDiv ϖ ε₁)
          (ML2Spine.spineCount ϖ ε₁) a b m := by
  classical
  have hsp := ML2Spine.spineRung_isSpine hβ0 hβ1 hϖ hε₁ hgain hdens
  have he0 : 0 < ML2Spine.spineDiv ϖ ε₁ := hsp.div_pos
  have hNpos : 0 < ML2Spine.spineCount ϖ ε₁ := by
    have := hsp.four_thousand_le_stepCount
    omega
  have hNR : (0 : ℝ) < (ML2Spine.spineCount ϖ ε₁ : ℝ) := by exact_mod_cast hNpos
  have heN : ML2Spine.spineDiv ϖ ε₁ ^ 2 * (ML2Spine.spineCount ϖ ε₁ : ℝ) = 1 := by
    rw [hsp.div_eq]
    rw [div_pow, one_pow, Real.sq_sqrt hNR.le]
    field_simp
  have he1 : ML2Spine.spineDiv ϖ ε₁ ≤ 1 := by
    have := ML2Spine.spineDiv_le_one hϖ hε₁
    linarith
  have hstep : ∀ j : ℕ, j + 1 ≤ ML2Spine.spineCount ϖ ε₁ →
      ML2Spine.spineRung β ϖ ε₁ gain dens j
        ≤ ((⌈ML2Spine.spineDiv ϖ ε₁
              * ((⌈ML2Spine.spineDiv ϖ ε₁ * (Tube.ssfGridLen δ : ℝ)⌉₊ : ℕ) : ℝ)⌉₊ : ℕ) : ℝ)
            / (Tube.ssfGridLen δ : ℝ) * ML2Spine.spineRung β ϖ ε₁ gain dens (j + 1) := by
    intro j hjN
    have h1 := rung_le_sq_mul_succ hsp hβ0 hβ1 (k := j) (by omega)
    have h2 := sq_le_margin_div he0 hLpos
    have h3 : 0 < ML2Spine.spineRung β ϖ ε₁ gain dens (j + 1) := hsp.rung_pos (j + 1)
    nlinarith
  refine isKatzTaoAtEveryScale_or_dividingWindow_run hδ0 hδ1 h4 hLpos 𝒰 hs hball he0 he1 heN
    (rinv := fun p c => (Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ)
      / (Tube.gridScale δ (Tube.ssfGridLen δ) c : ℝ))
    (fun _ _ => rfl)
    (fun a b hab => one_le_gridRatio hδ0 hδ1.le hab.le)
    (fun j j' hjj' => hsp.rung_mono hjj') (fun j => (hsp.rung_pos j).le) hsp.rung_le_div
    (Efac := 1) le_rfl
    (sourceBound_calibration hδ0 hδ1.le hLpos (fun j => (hsp.rung_pos j).le) hstep
      (fun _ _ => rfl))
    hGood hD1 hcrude hCstarChain hwindow hband

end SpineDichotomy

section FibreRows

universe u

variable {ι : Type u} {δ Cu : NNReal}

/-- **The five source-assumed rows, on one tower.** -/
def FibreWindowRows {t : Finset ι} {W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (β ϖ ε₁ η' κ : ℝ) (gain dens : ℝ → ℝ) (Cstar D : ENNReal)
    (𝒲 : Tube.UniformTubeSet t (fun i => (W i).toTube) (Tube.ssfGridLen δ) Cu) : Prop :=
  -- (H3), source l.2683-2684: the assumed top-cell estimate
  (towerDensityArrayFibre 𝒲 0 (Tube.ssfGridLen δ)
      ≤ ENNReal.ofReal (((Tube.gridScale δ (Tube.ssfGridLen δ) 0 : ℝ)
          / (Tube.gridScale δ (Tube.ssfGridLen δ) (Tube.ssfGridLen δ) : ℝ))
        ^ ML2Spine.spineRung β ϖ ε₁ gain dens 0)) ∧
  -- (H2), source l.2679-2681: the assumed cardinality estimate at the crude exponent `d = 4`
  (∀ p c : ℕ, p ≤ c → c ≤ Tube.ssfGridLen δ →
      towerDensityArrayFibre 𝒲 p c ≤ D * ENNReal.ofReal
        (((Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ)
          / (Tube.gridScale δ (Tube.ssfGridLen δ) c : ℝ)) ^ (4 : ℕ))) ∧
  -- `le_window_maxDensity`, reduced by `window_field_of_card` to the count
  (∀ a b m : ℕ, ∀ ρ : NNReal,
      (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
          * ((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
            / (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)) ^ ML2Spine.spineDiv ϖ ε₁ ≤ (ρ : ℝ) →
      (ρ : ℝ) ≤ (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
          * ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
            / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) ^ ML2Spine.spineDiv ϖ ε₁ →
      ∀ j ∈ 𝒲.cover.indexSet a,
        ENNReal.ofReal (((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ) / (ρ : ℝ))
            ^ ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1))
          ≤ Cstar * Kakeya.maxDensity (𝒲.nodesUnder b a j)
              (fun j' => ((𝒲.cover.tube b j').rescale ρ).toConvexSpaceBody)) ∧
  -- `FillAt`, the source's fullness clause (l.4030-4031)
  (∀ a b : ℕ, ∀ jθ ∈ 𝒲.cover.indexSet a, ∀ jp ∈ 𝒲.nodesUnder a a jθ, ∀ m' : ℕ,
      a < m' → m' ≤ b → FillAt 𝒲 κ a m' jp) ∧
  -- the `hclose` scalar row
  (∀ a b m : ℕ, ∀ m' : ℕ, a + ⌈ML2Spine.spineDiv ϖ ε₁ * ((b : ℝ) - (a : ℝ))⌉₊ ≤ m' → a < m' →
      m' ≤ b →
      ENNReal.ofReal (((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
              / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ))
            ^ (4 * (ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1) / 16)))
          * (Cstar ^ 2 * ENNReal.ofReal (twoScaleConst.{u, 0} (EuclideanSpace ℝ (Fin 3)) ^ 2)
              * (Cu : ENNReal) * (δ : ENNReal) ^ (-(2 * η'))
              * ((Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : NNReal)
                : ENNReal))
        ≤ ENNReal.ofReal (((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
              / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ))
            ^ ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1))
          * ENNReal.ofReal κ
          * ((Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : NNReal)
            : ENNReal))

end FibreRows

section Producer

universe u

variable {ι : Type u} {δ Cu : NNReal} {v : Finset ι}
  {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}

open scoped Classical in
/-- **`RefinedSupplyAt`, produced from the tree's inputs.** -/
theorem refinedSupplyAt_of_fibreRows {β ϖ ε₁ η' κ : ℝ} {gain dens : ℝ → ℝ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    (hη' : 0 < η') (hκ : 0 < κ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (h4 : 4 * Tube.gridScale δ (Tube.ssfGridLen δ) 1 ≤ 1) (hLpos : 0 < Tube.ssfGridLen δ)
    {C : NNReal} {Kl cl : ℕ} {Λf : ℝ≥0∞} {D : ENNReal} (hD1 : 1 ≤ D)
    {𝒰 : Tube.UniformTubeSet v (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu}
    (hCstarChain : (Cu : ENNReal)
        * fibreChainConst.{u} ^ (ML2Spine.spineCount ϖ ε₁ + 1)
      ≤ (C : ENNReal) * StickyKakeya.totalLoss C Kl cl δ)
    (hCuη : (Cu : ENNReal) ≤ (δ : ENNReal) ^ (-(2 * η')))
    (hCstarNu : (C : ENNReal) * StickyKakeya.totalLoss C Kl cl δ
      ≤ (δ : ENNReal) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens / 20)))
    (hcap : ∀ m : ℕ, η' ≤ ML2Spine.spineDiv ϖ ε₁ ^ 2
      * ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1) / 64)
    (hpass : ∀ (S : Finset ι) (hS : S ⊆ v), S.Nonempty →
      ∀ (Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
        (ht : ∀ i, (Z i).toTube = (T i).toTube) (hh : IsClassHomogeneousOn 𝒰 S),
      ∃ (S' : Finset ι) (hS' : S' ⊆ S)
        (hhom : IsClassHomogeneousOn ((𝒰.restrictOccupied hS hh).retube (funext ht)) S'),
        IsShadedRefinementOf ((𝒰.restrictOccupied hS hh).retube (funext ht)) Λf S Z S' Z ∧
        ∃ Φ : ℕ → ℕ → ENNReal, ∀ p ≤ Tube.ssfGridLen δ, ∀ c ≤ Tube.ssfGridLen δ,
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
              ≤ (C : ENNReal) * StickyKakeya.totalLoss C Kl cl δ * Φ p c)
    (hrows : ∀ (t : Finset ι) (W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
      (𝒲 : Tube.UniformTubeSet t (fun i => (W i).toTube) (Tube.ssfGridLen δ) Cu), t.Nonempty →
      (∀ i ∈ t, ((W i).toTube).carrier
        ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) →
      FibreWindowRows β ϖ ε₁ η' κ gain dens
        ((C : ENNReal) * StickyKakeya.totalLoss C Kl cl δ) D 𝒲)
    (hball : ∀ i ∈ v, ((T i).toTube).carrier
      ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    RefinedSupplyAt (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ η' gain dens Λf
      ((Cu : ENNReal) * (fibreChainConst.{u} ^ (ML2Spine.spineCount ϖ ε₁ + 2)
        * (D * ENNReal.ofReal ((δ : ℝ) ^ (-(5 * ML2Spine.spineDiv ϖ ε₁)))))) 𝒰 := by
  classical
  refine refinedSupplyAt_of_dichotomy (fun S hS hne Z ht hh => ?_)
  obtain ⟨S', hS', hhom, href, Φ, hband⟩ := hpass S hS hne Z ht hh
  refine ⟨S', Z, hS', hhom, rfl, href, ?_⟩
  have hS'ne : S'.Nonempty := href.nonempty
  have hball' : ∀ i ∈ S', ((Z i).toTube).carrier
      ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
    intro i hi
    rw [ht i]
    exact hball i (hS (hS' hi))
  obtain ⟨hGood, hcrude, hwindow, hfill, hclose⟩ :=
    hrows S' Z (refinedHierarchy ((𝒰.restrictOccupied hS hh).retube (funext ht)) hS' hhom rfl)
      hS'ne hball'
  rcases isKatzTaoAtEveryScale_or_dividingWindow_spine hβ0 hβ1 hϖ hε₁ hgain hdens hδ0 hδ1
    h4 hLpos _ hS'ne hball' hCstarChain hGood hD1 hcrude hwindow hband with hev | ⟨a, b, m, hwin⟩
  · exact Or.inl hev
  · exact Or.inr ⟨a, b, m, hwin,
      floorHypothesisAt_of_fibreWindow hβ0 hβ1 hϖ hε₁ hgain hdens hη' hκ hδ0 hδ1 h4 _ hS'ne
        hball' hCuη hwin hCstarNu (hcap m) (hfill a b) (hclose a b m)⟩

open scoped Classical in
/-- **`RefinedFloorSupplyAt`, produced** — the payload row `RefinedFloorPayload` quantifies. -/
theorem refinedFloorSupplyAt_of_fibreRows {β ϖ ε₁ η' κ : ℝ} {gain dens : ℝ → ℝ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    (hη' : 0 < η') (hκ : 0 < κ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (h4 : 4 * Tube.gridScale δ (Tube.ssfGridLen δ) 1 ≤ 1) (hLpos : 0 < Tube.ssfGridLen δ)
    {C : NNReal} {Kl cl : ℕ} {Λf : ℝ≥0∞} {D : ENNReal} (hD1 : 1 ≤ D)
    {𝒰 : Tube.UniformTubeSet v (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu}
    (hCstarChain : (Cu : ENNReal)
        * fibreChainConst.{u} ^ (ML2Spine.spineCount ϖ ε₁ + 1)
      ≤ (C : ENNReal) * StickyKakeya.totalLoss C Kl cl δ)
    (hCuη : (Cu : ENNReal) ≤ (δ : ENNReal) ^ (-(2 * η')))
    (hCstarNu : (C : ENNReal) * StickyKakeya.totalLoss C Kl cl δ
      ≤ (δ : ENNReal) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens / 20)))
    (hcap : ∀ m : ℕ, η' ≤ ML2Spine.spineDiv ϖ ε₁ ^ 2
      * ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1) / 64)
    (hpass : ∀ (S : Finset ι) (hS : S ⊆ v), S.Nonempty →
      ∀ (Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
        (ht : ∀ i, (Z i).toTube = (T i).toTube) (hh : IsClassHomogeneousOn 𝒰 S),
      ∃ (S' : Finset ι) (hS' : S' ⊆ S)
        (hhom : IsClassHomogeneousOn ((𝒰.restrictOccupied hS hh).retube (funext ht)) S'),
        IsShadedRefinementOf ((𝒰.restrictOccupied hS hh).retube (funext ht)) Λf S Z S' Z ∧
        ∃ Φ : ℕ → ℕ → ENNReal, ∀ p ≤ Tube.ssfGridLen δ, ∀ c ≤ Tube.ssfGridLen δ,
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
              ≤ (C : ENNReal) * StickyKakeya.totalLoss C Kl cl δ * Φ p c)
    (hrows : ∀ (t : Finset ι) (W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
      (𝒲 : Tube.UniformTubeSet t (fun i => (W i).toTube) (Tube.ssfGridLen δ) Cu), t.Nonempty →
      (∀ i ∈ t, ((W i).toTube).carrier
        ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) →
      FibreWindowRows β ϖ ε₁ η' κ gain dens
        ((C : ENNReal) * StickyKakeya.totalLoss C Kl cl δ) D 𝒲)
    (hball : ∀ i ∈ v, ((T i).toTube).carrier
      ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (hno : ∀ {S' : Finset ι} {W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
      (V : Tube.UniformTubeSet S' (fun i => (W i).toTube) (Tube.ssfGridLen δ) Cu),
      ¬ V.IsKatzTaoAtEveryScale ((Cu : ENNReal)
        * (fibreChainConst.{u} ^ (ML2Spine.spineCount ϖ ε₁ + 2)
          * (D * ENNReal.ofReal ((δ : ℝ) ^ (-(5 * ML2Spine.spineDiv ϖ ε₁))))))) :
    RefinedFloorSupplyAt (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ η' gain dens Λf 𝒰 :=
  refinedFloorSupplyAt_of_refinedSupplyAt
    (refinedSupplyAt_of_fibreRows hβ0 hβ1 hϖ hε₁ hgain hdens hη' hκ hδ0 hδ1 h4 hLpos hD1
      hCstarChain hCuη hCstarNu hcap hpass hrows hball) hno

/-- **`FloorDataAtTrichotomy`, produced end to end** — the payload side of `GeometricCoreAt`. -/
theorem floorDataAtTrichotomy_of_fibreRows {β ϖ ε₁ η' κ h : ℝ} {gain dens : ℝ → ℝ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    (hη' : 0 < η') (hκ : 0 < κ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (h4 : 4 * Tube.gridScale δ (Tube.ssfGridLen δ) 1 ≤ 1) (hLpos : 0 < Tube.ssfGridLen δ)
    {C : NNReal} {Kl cl : ℕ} {Λf : ℝ≥0∞} {D : ENNReal} (hD1 : 1 ≤ D)
    {𝒰 : Tube.UniformTubeSet v (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu}
    (hCstarChain : (Cu : ENNReal)
        * fibreChainConst.{u} ^ (ML2Spine.spineCount ϖ ε₁ + 1)
      ≤ (C : ENNReal) * StickyKakeya.totalLoss C Kl cl δ)
    (hCuη : (Cu : ENNReal) ≤ (δ : ENNReal) ^ (-(2 * η')))
    (hCstarNu : (C : ENNReal) * StickyKakeya.totalLoss C Kl cl δ
      ≤ (δ : ENNReal) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens / 20)))
    (hcap : ∀ m : ℕ, η' ≤ ML2Spine.spineDiv ϖ ε₁ ^ 2
      * ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1) / 64)
    (hpass : ∀ (S : Finset ι) (hS : S ⊆ v), S.Nonempty →
      ∀ (Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
        (ht : ∀ i, (Z i).toTube = (T i).toTube) (hh : IsClassHomogeneousOn 𝒰 S),
      ∃ (S' : Finset ι) (hS' : S' ⊆ S)
        (hhom : IsClassHomogeneousOn ((𝒰.restrictOccupied hS hh).retube (funext ht)) S'),
        IsShadedRefinementOf ((𝒰.restrictOccupied hS hh).retube (funext ht)) Λf S Z S' Z ∧
        ∃ Φ : ℕ → ℕ → ENNReal, ∀ p ≤ Tube.ssfGridLen δ, ∀ c ≤ Tube.ssfGridLen δ,
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
              ≤ (C : ENNReal) * StickyKakeya.totalLoss C Kl cl δ * Φ p c)
    (hrows : ∀ (t : Finset ι) (W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
      (𝒲 : Tube.UniformTubeSet t (fun i => (W i).toTube) (Tube.ssfGridLen δ) Cu), t.Nonempty →
      (∀ i ∈ t, ((W i).toTube).carrier
        ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) →
      FibreWindowRows β ϖ ε₁ η' κ gain dens
        ((C : ENNReal) * StickyKakeya.totalLoss C Kl cl δ) D 𝒲)
    (hball : ∀ i ∈ v, ((T i).toTube).carrier
      ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (hno : ∀ {S' : Finset ι} {W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
      (V : Tube.UniformTubeSet S' (fun i => (W i).toTube) (Tube.ssfGridLen δ) Cu),
      ¬ V.IsKatzTaoAtEveryScale ((Cu : ENNReal)
        * (fibreChainConst.{u} ^ (ML2Spine.spineCount ϖ ε₁ + 2)
          * (D * ENNReal.ofReal ((δ : ℝ) ^ (-(5 * ML2Spine.spineDiv ϖ ε₁))))))) :
    FloorDataAtTrichotomy (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ η' h gain dens Λf 𝒰 :=
  floorDataAtTrichotomy_of_refinedFloorSupply
    (refinedFloorSupplyAt_of_fibreRows hβ0 hβ1 hϖ hε₁ hgain hdens hη' hκ hδ0 hδ1 h4 hLpos hD1
      hCstarChain hCuη hCstarNu hcap hpass hrows hball hno)

end Producer

section Controls

universe u

variable {ι : Type u} {δ : NNReal}

/-- **Firing control, and the reason this file exists: the *universally* quantified calibration is
unsatisfiable.** -/
theorem universal_calibration_fails (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hLpos : 0 < Tube.ssfGridLen δ) {η : ℕ → ℝ} {j : ℕ} (hη : 0 < η j)
    {b : ℕ} (hb0 : 0 < b) :
    ¬ (ENNReal.ofReal (1 : ℝ)
        * sourceBound (fun p c => (Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ)
            / (Tube.gridScale δ (Tube.ssfGridLen δ) c : ℝ)) η j 0 b
      ≤ sourceBound (fun p c => (Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ)
            / (Tube.gridScale δ (Tube.ssfGridLen δ) c : ℝ)) η (j + 1) b b) := by
  have hu0 : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
  have hu1 : (δ : ℝ) < 1 := by exact_mod_cast hδ1
  have hbpos : (0 : ℝ) < (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ) := by
    exact_mod_cast Tube.gridScale_pos hδ0 _ b
  have hlt : (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ) < 1 := by
    have := Tube.gridScale_lt_gridScale hδ0 hδ1 hLpos (k := 0) (l := b) hb0
    have h0 : (Tube.gridScale δ (Tube.ssfGridLen δ) 0 : NNReal) = 1 := Tube.gridScale_zero δ _
    rw [h0] at this
    exact_mod_cast this
  have hRHS : sourceBound (fun p c => (Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ)
      / (Tube.gridScale δ (Tube.ssfGridLen δ) c : ℝ)) η (j + 1) b b = 1 := by
    rw [sourceBound]
    have : (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
        / (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ) = 1 := by field_simp
    rw [this, Real.one_rpow, ENNReal.ofReal_one]
  have hLHSbig : (1 : ℝ) < ((Tube.gridScale δ (Tube.ssfGridLen δ) 0 : ℝ)
      / (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)) ^ η j := by
    have h0 : (Tube.gridScale δ (Tube.ssfGridLen δ) 0 : ℝ) = 1 := by
      rw [Tube.gridScale_zero]; norm_num
    rw [h0]
    refine Real.one_lt_rpow_iff_of_pos (by positivity) |>.mpr ?_
    exact Or.inl ⟨by rw [lt_div_iff₀ hbpos, one_mul]; exact hlt, hη⟩
  rw [ENNReal.ofReal_one, one_mul, hRHS, sourceBound]
  intro hcon
  have := (ENNReal.ofReal_le_one).mp hcon
  linarith

end Controls

end Kakeya.ML2Core

end

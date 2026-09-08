/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorTwoScale
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorParent
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorBand
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorBookkeeping
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorExponents
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineEDMultBound

/-!
# The count floor at the genuine parent (Stage 2, rows F4a and F6(iv) of )

Alternative (F) of the refined source's `lem:ml2-window-refinement` (l.4062-4076; the floor
`eq:ml2-count-floor`, l.4074 and l.4474-4482): at the genuine parent `p`, every level-`p` cell under
a level-`a` node carries at least `(ρ_p/ρ_{m'})^{2+4ζ}` level-`m'` cells, for every window level
`m'`.  This leaf derives that floor — the existing `hfloor` clause 4, byte for byte — from the window
twin and two named binders, and compiles the exponent closure the derivation spends.

* `FillAt`: at a
  cell `T_k` the maximal density of the level-`c` cells inside it is attained, up to `κ`, **on the
  cell itself**.  Both sides are densities of the same unrestricted `Finset`; the engine that
  produces it is `Kakeya.ML2Core.exists_biasedMaximizer_densityIn_ge` (G2′), which selects no
  subfamily.
* `ofReal_ratio_le_maxDensity_nodesUnder_parent`: the chain W1 → F1 → F1b → F3 of  — the twin's level clause at `m'`, the two-scale bound through the level-`p` ancestors, the
  ancestors' density through `ParentAdmissible`, and the band at the pair `(p, m')` — ending at
  `Δ_max(𝕊_{m'}⟨T_p⟩)` of the **given** cell `jp`.
* `floor_exponent_closes` (F6(iv)): the closure `hclose` is a threshold fact, discharged below
  `δ₀(β, ϖ, ε₁, gain, dens, κ, Cu₀, C₀)` on the ceiling window; the margin is `> 0.71·e²τ`
  (`3e²τ/4 − e²τ/32 − ν/10 ≥ (7359/10240)·e²τ`, with `Θ ≥ δ^{-e²}` from
  `ratio_ge_of_ceil_window`, `2η' ≤ e²τ/32` from the cap and `ν ≤ e²βτ₁/1024` from the estimate
  re-anchor; here spent as `e²τ₁/2`).
* `floor_of_windowLevels_of_fill` (F4a): the floor from `hwin`, `hCstar`, `hcap`, `hgap`, `hpar`,
  `hfill` and `hclose`, conclusion to existing `hfloor` clause 4 (C-F4a).

Two departures from /, both recorded for source:
(i) `u.Nonempty` and the unit-ball hypothesis are binders — F1 (`exists_twoScale_nodesUnder`) and
F1b require them and neither follows from `jθ ∈ 𝒰.cover.indexSet a`; they are the trial's standard
data (F7 carries both);
(ii) `hclose` is stated in the constants the fill derivation buys — `Cu` to the first power and
`κ` itself — and only on W1's own ceiling window `a + ⌈ε(b−a)⌉₊ ≤ m'` (off that window
`Θ_{m'} = ρ_a/ρ_{m'}` can be `≈ e²`, and no threshold discharges the closure there).  the form
(`Cu²`, `κ^{1+ε_b}`) implies this one whenever `1 ≤ Cu` and `κ ≤ 1`; with `FillAt` there is no bias
and hence no `ε_b` anywhere in F4a.  One `κ` serves `hfill` and `hclose` (C-F4e).
-/

@[expose] public section

open MeasureTheory Tube Topology Filter
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

universe u v

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type u} {δ : NNReal}

/-! ### H5′ — the fill clause -/

/-- **H5′ -- the geometric core, in the form the tree can produce and consume.**  At the genuine
parent the maximal density of the level-`m'` cells inside a `p`-cell is attained, up to `κ`, **on
the cell itself**: `Δ_max(𝕊_{m'}⟨T_p⟩) ≤ κ⁻¹ Δ(𝕊_{m'}⟨T_p⟩, T_p)`.  Since every such cell *is*
inside `T_p`, `Δ(·, T_p) · |T_p| = Σ|V|` exactly (`Kakeya.sum_volume_eq_densityIn_mul_volume'`), so
this is literally the count floor's missing `(ρ_p/ρ_{m'})²` and nothing else. -/
def FillAt {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {C : NNReal}
    (𝒰 : Tube.UniformTubeSet s T N C) (κ : ℝ) (k c : ℕ) (j : ι) : Prop :=
  ENNReal.ofReal κ *
      Kakeya.maxDensity (𝒰.nodesUnder c k j) (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)
    ≤ Kakeya.densityIn (𝒰.nodesUnder c k j) (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)
        (𝒰.cover.tube k j).toConvexSpaceBody

/-! ### The chain W1 → F1 → F1b → F3 -/

open scoped Classical in
/-- **The window's level clause reaches the given `p`-cell.**  From the twin's `le_level_maxDensity`
at a window level `m'` (W1), through the two-scale bound at the constant `twoScaleConst` (F1), the
ancestors' density `≤ Cu · δ^{-2η'}` (F1b + `ParentAdmissible`), and the band at the pair `(p, m')`
(F3): `(ρ_a/ρ_{m'})^{η_{m+1}} ≤ Cstar² · C₀² · Cu · δ^{-2η'} · Δ_max(𝕊_{m'}⟨T_p⟩)` at **every**
level-`p` cell `jp`.  Ancestors outside `𝒰.cover.indexSet p` have empty class and contribute `0`. -/
theorem ofReal_ratio_le_maxDensity_nodesUnder_parent
    {Cu : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {u : Finset ι} {T : ι → Tube δ E}
    (𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu) (hs : u.Nonempty)
    (hball : ∀ i ∈ u, (T i).carrier ⊆ Metric.closedBall (0 : E) 1)
    {Cstar : ENNReal} {η : ℕ → ℝ} {εd : ℝ} {N a b m : ℕ}
    (hwin : ML2Reduction.IsKatzTaoDividingWindowLevels 𝒰 Cstar η εd N a b m)
    (hCtop : Cstar ≠ ⊤) {η' : ℝ} {p : ℕ} (hap : a ≤ p) (hpar : ParentAdmissible 𝒰 η' a p)
    {m' : ℕ} (hpm' : p ≤ m') (hm'N : m' ≤ Tube.ssfGridLen δ)
    (hgap : 4 * Tube.gridScale δ (Tube.ssfGridLen δ) m' ≤ Tube.gridScale δ (Tube.ssfGridLen δ) p)
    (hlo : a + ⌈εd * ((b : ℝ) - (a : ℝ))⌉₊ ≤ m') (hhi : m' + ⌈εd * ((b : ℝ) - (a : ℝ))⌉₊ ≤ b)
    {jθ : ι} (hjθ : jθ ∈ 𝒰.cover.indexSet a) {jp : ι} (hjp : jp ∈ 𝒰.cover.indexSet p) :
    ENNReal.ofReal (((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
          / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ)) ^ η (m + 1))
      ≤ Cstar ^ 2 * ENNReal.ofReal (twoScaleConst.{u, v} E) ^ 2 * (Cu : ENNReal)
          * (δ : ENNReal) ^ (-(2 * η'))
          * Kakeya.maxDensity (𝒰.nodesUnder m' p jp)
              (fun j' => (𝒰.cover.tube m' j').toConvexSpaceBody) := by
  have hpN : p ≤ Tube.ssfGridLen δ := hpm'.trans hm'N
  -- W1
  have hW1 := hwin.le_level_maxDensity m' hlo hhi jθ hjθ
  -- F1 at the named constant
  have hF1 := twoScaleConst_spec (E := E) hδ0 hδ1 𝒰 hs hball (a := a) hpm' hm'N hgap jθ
  -- F1b, then the parent's admissibility on every level-`a` node
  have hF1b := maxDensity_ancestors_le_mul_sup 𝒰 hs hap hpm' hm'N jθ
  have hsupA : (𝒰.cover.indexSet a).sup (fun j' => Kakeya.maxDensity (𝒰.nodesUnder p a j')
      (fun jp => (𝒰.cover.tube p jp).toConvexSpaceBody)) ≤ (δ : ENNReal) ^ (-(2 * η')) :=
    Finset.sup_le (fun j' hj' => hpar j' hj')
  -- F3 at every ancestor, with the twin's constant read as a real constant
  have hC'eq : Cstar = ((Cstar.toNNReal : NNReal) : ENNReal) := (ENNReal.coe_toNNReal hCtop).symm
  have hSUP : ((𝒰.nodesUnder m' a jθ).image (ML2Reduction.coarseNode 𝒰.cover.toChain p m')).sup
      (fun jp' => Kakeya.maxDensity
        ((coverClass u (𝒰.cover.assign p) jp').image (𝒰.cover.assign m'))
        (fun j' => (𝒰.cover.tube m' j').toConvexSpaceBody))
      ≤ Cstar * Kakeya.maxDensity (𝒰.nodesUnder m' p jp)
          (fun j' => (𝒰.cover.tube m' j').toConvexSpaceBody) := by
    refine Finset.sup_le (fun jp' _ => ?_)
    by_cases hmem : jp' ∈ 𝒰.cover.indexSet p
    · have h := le_maxDensity_nodesUnder_of_windowLevels 𝒰 hwin hC'eq hpm' hm'N
        (X := Kakeya.maxDensity
          ((coverClass u (𝒰.cover.assign p) jp').image (𝒰.cover.assign m'))
          (fun j' => (𝒰.cover.tube m' j').toConvexSpaceBody)) (D := 1)
        ⟨jp', hmem, by rw [one_mul]⟩ jp hjp
      rwa [one_mul, ← hC'eq] at h
    · have hempty : coverClass u (𝒰.cover.assign p) jp' = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro i hi
        simp only [coverClass, Finset.mem_filter] at hi
        exact hmem (hi.2 ▸ 𝒰.cover.assign_mem p hpN i hi.1)
      rw [hempty, Finset.image_empty, Kakeya.maxDensity_empty]
      exact bot_le
  calc ENNReal.ofReal (((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
          / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ)) ^ η (m + 1))
      ≤ Cstar * Kakeya.maxDensity (𝒰.nodesUnder m' a jθ)
          (fun j' => (𝒰.cover.tube m' j').toConvexSpaceBody) := hW1
    _ ≤ Cstar * (ENNReal.ofReal (twoScaleConst.{u, v} E) ^ 2
          * ((Cu : ENNReal) * (δ : ENNReal) ^ (-(2 * η')))
          * (Cstar * Kakeya.maxDensity (𝒰.nodesUnder m' p jp)
              (fun j' => (𝒰.cover.tube m' j').toConvexSpaceBody))) :=
        mul_le_mul' le_rfl (hF1.trans (mul_le_mul'
          (mul_le_mul' le_rfl (hF1b.trans (mul_le_mul' le_rfl hsupA))) hSUP))
    _ = _ := by ring

/-! ### F6(iv) — the exponent closure -/

/-- **The closure's arithmetic, in `ℝ`**.  With `Θ ≥ δ^{-e²}`, `Θ_p ≤ Θ`,
`Cs ≤ δ^{-ν/20}`, `2η' ≤ e²τ/32`, `ν ≤ e²τ₁/1024` and `τ₁ ≤ τ`, the closure holds as soon as the
`δ`-free constant `C₀²·Cu₀·C_vol/(κ·c_vol)` is below `δ^{-e²τ₁/2}`: the exponent margin
`3e²τ/4 − e²τ/32 − ν/10` exceeds `e²τ₁/2` (indeed `(7359/10240)·e²τ`). -/
theorem floor_exponent_closes_real {δ e τ τ₁ ν η' κ C₀ Cs Cu Cu₀ Cv cv Θ Θp : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (he : 0 < e) (hτ₁ : 0 < τ₁) (hτ : τ₁ ≤ τ)
    (hν0 : 0 ≤ ν) (hν : ν ≤ e ^ 2 * τ₁ / 1024) (hη' : 2 * η' ≤ e ^ 2 * τ / 32)
    (hκ : 0 < κ) (hC₀ : 0 < C₀) (hCs0 : 0 ≤ Cs) (hCs : Cs ≤ δ ^ (-(ν / 20)))
    (hCu0 : 0 ≤ Cu) (hCu : Cu ≤ Cu₀) (hCv : 0 ≤ Cv) (hcv : 0 < cv)
    (hΘ : δ ^ (-(e ^ 2)) ≤ Θ) (hΘp0 : 0 ≤ Θp) (hΘp : Θp ≤ Θ)
    (hthr : C₀ ^ 2 * Cu₀ * Cv / (κ * cv) ≤ δ ^ (-(e ^ 2 * τ₁ / 2))) :
    Θp ^ (4 * (τ / 16)) * (Cs ^ 2 * C₀ ^ 2 * Cu * δ ^ (-(2 * η')) * Cv) ≤ Θ ^ τ * κ * cv := by
  have hτ0 : 0 < τ := hτ₁.trans_le hτ
  have hΘ0 : 0 < Θ := (Real.rpow_pos_of_pos hδ0 _).trans_le hΘ
  have he2 : 0 < e ^ 2 := by positivity
  have hCu₀ : 0 ≤ Cu₀ := hCu0.trans hCu
  have h1 : Θp ^ (4 * (τ / 16)) ≤ Θ ^ (4 * (τ / 16)) :=
    Real.rpow_le_rpow hΘp0 hΘp (by positivity)
  have h2 : Cs ^ 2 ≤ δ ^ (-(ν / 10)) := by
    calc Cs ^ 2 ≤ (δ ^ (-(ν / 20))) ^ 2 := by gcongr
      _ = δ ^ (-(ν / 10)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hδ0.le]; congr 1; push_cast; ring
  have h3 : δ ^ (-(2 * η')) ≤ δ ^ (-(e ^ 2 * τ / 32)) :=
    Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1.le (by linarith)
  have h4 : δ ^ (-(3 * e ^ 2 * τ / 4)) ≤ Θ ^ (3 * τ / 4) := by
    calc δ ^ (-(3 * e ^ 2 * τ / 4)) = (δ ^ (-(e ^ 2))) ^ (3 * τ / 4) := by
          rw [← Real.rpow_mul hδ0.le]; congr 1; ring
      _ ≤ Θ ^ (3 * τ / 4) := Real.rpow_le_rpow (by positivity) hΘ (by positivity)
  have hM : e ^ 2 * τ₁ / 2 ≤ 3 * e ^ 2 * τ / 4 - e ^ 2 * τ / 32 - ν / 10 := by
    have : e ^ 2 * τ₁ ≤ e ^ 2 * τ := mul_le_mul_of_nonneg_left hτ he2.le
    nlinarith
  have h5 : δ ^ (-(e ^ 2 * τ₁ / 2))
      ≤ δ ^ (-(3 * e ^ 2 * τ / 4 - e ^ 2 * τ / 32 - ν / 10)) :=
    Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1.le (by linarith)
  have hK : C₀ ^ 2 * Cu₀ * Cv
      ≤ δ ^ (-(3 * e ^ 2 * τ / 4 - e ^ 2 * τ / 32 - ν / 10)) * (κ * cv) := by
    have := hthr.trans h5
    rwa [div_le_iff₀ (by positivity)] at this
  have hp1 : 0 < δ ^ (-(ν / 10)) := Real.rpow_pos_of_pos hδ0 _
  have hp2 : 0 < δ ^ (-(e ^ 2 * τ / 32)) := Real.rpow_pos_of_pos hδ0 _
  have hcomb : δ ^ (-(ν / 10)) * δ ^ (-(e ^ 2 * τ / 32))
      * δ ^ (-(3 * e ^ 2 * τ / 4 - e ^ 2 * τ / 32 - ν / 10)) = δ ^ (-(3 * e ^ 2 * τ / 4)) := by
    rw [← Real.rpow_add hδ0, ← Real.rpow_add hδ0]; congr 1; ring
  have hΘsplit : Θ ^ (4 * (τ / 16)) * Θ ^ (3 * τ / 4) = Θ ^ τ := by
    rw [← Real.rpow_add hΘ0]; congr 1; ring
  calc Θp ^ (4 * (τ / 16)) * (Cs ^ 2 * C₀ ^ 2 * Cu * δ ^ (-(2 * η')) * Cv)
      ≤ Θ ^ (4 * (τ / 16))
          * (δ ^ (-(ν / 10)) * C₀ ^ 2 * Cu₀ * δ ^ (-(e ^ 2 * τ / 32)) * Cv) := by
        refine mul_le_mul h1 ?_ (by positivity) (by positivity)
        refine mul_le_mul_of_nonneg_right ?_ hCv
        refine mul_le_mul ?_ h3 (by positivity) (by positivity)
        refine mul_le_mul ?_ hCu hCu0 (by positivity)
        exact mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = Θ ^ (4 * (τ / 16))
          * (δ ^ (-(ν / 10)) * δ ^ (-(e ^ 2 * τ / 32)) * (C₀ ^ 2 * Cu₀ * Cv)) := by ring
    _ ≤ Θ ^ (4 * (τ / 16))
          * (δ ^ (-(ν / 10)) * δ ^ (-(e ^ 2 * τ / 32))
            * (δ ^ (-(3 * e ^ 2 * τ / 4 - e ^ 2 * τ / 32 - ν / 10)) * (κ * cv))) := by
        gcongr
    _ = Θ ^ (4 * (τ / 16)) * (δ ^ (-(3 * e ^ 2 * τ / 4)) * (κ * cv)) := by
        rw [← hcomb]; ring
    _ ≤ Θ ^ (4 * (τ / 16)) * (Θ ^ (3 * τ / 4) * (κ * cv)) := by gcongr
    _ = Θ ^ τ * κ * cv := by rw [← hΘsplit]; ring

/-- **F6(iv) — the exponent closure `hclose`, discharged below a threshold.**  For
`β, ϖ, ε₁, gain, dens, κ, Cu₀, C₀` fixed before `δ`: eventually as `δ → 0⁺`, for every hierarchy
constant `Cu ≤ Cu₀`, every `Cstar ≤ δ^{-ν/20}`, every `ε_div`-separated window `a < b ≤ N`, every
`η'` under the cap, every `p ≥ a` and every level `m'` on W1's ceiling window with `p < m'`,
`(ρ_p/ρ_{m'})^{4ζ} · Cstar²·C₀²·Cu·δ^{-2η'}·C_vol ≤ (ρ_a/ρ_{m'})^{η_{m+1}} · κ · c_vol`.
The suppliers are `ratio_ge_of_ceil_window` (`Θ ≥ δ^{-e²}`, stronger than the source's l.4117
`/2`), the cap (`2η' ≤ e²τ/32`) and the re-anchored `spineNu_le_step_bound`; the factor-`4` gap
lemmas play no part here. -/
theorem floor_exponent_closes {β ϖ ε₁ : ℝ} {gain dens : ℝ → ℝ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    {κ : ℝ} (hκ : 0 < κ) (Cu₀ : NNReal) {C₀ : ℝ} (hC₀ : 0 < C₀) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {Cu : NNReal}, Cu ≤ Cu₀ → ∀ {Cstar : ENNReal},
        Cstar ≤ (δ : ENNReal) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens / 20)) →
      ∀ {a b m : ℕ}, a < b → b ≤ Tube.ssfGridLen δ →
        (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
          ≤ (δ : ℝ) ^ ML2Spine.spineDiv ϖ ε₁ * (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ) →
      ∀ {η' : ℝ},
        η' ≤ ML2Spine.spineDiv ϖ ε₁ ^ 2 * ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1) / 64 →
      ∀ {p : ℕ}, a ≤ p →
      ∀ m' : ℕ, a + ⌈ML2Spine.spineDiv ϖ ε₁ * ((b : ℝ) - (a : ℝ))⌉₊ ≤ m' → p < m' →
        ENNReal.ofReal (((Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ))
              ^ (4 * (ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1) / 16)))
            * (Cstar ^ 2 * ENNReal.ofReal (C₀ ^ 2) * (Cu : ENNReal)
                * (δ : ENNReal) ^ (-(2 * η'))
                * ((Tube.volume_le.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : NNReal)
                  : ENNReal))
          ≤ ENNReal.ofReal (((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ))
              ^ ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1))
            * ENNReal.ofReal κ
            * ((Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : NNReal)
              : ENNReal) := by
  -- the spine's exponents
  have he : 0 < ML2Spine.spineDiv ϖ ε₁ := ML2Spine.spineDiv_pos hϖ hε₁
  have hsp := ML2Spine.spineRung_isSpine hβ0 hβ1 hϖ hε₁ hgain hdens
  have hτ₁ : 0 < ML2Spine.spineRung β ϖ ε₁ gain dens 1 := hsp.rung_pos 1
  have hν0 : 0 < ML2Spine.spineNu β ϖ ε₁ gain dens := ML2Spine.spineNu_pos hβ0 hϖ hε₁ hgain hdens
  have hνle : ML2Spine.spineNu β ϖ ε₁ gain dens
      ≤ ML2Spine.spineDiv ϖ ε₁ ^ 2 * ML2Spine.spineRung β ϖ ε₁ gain dens 1 / 1024 := by
    have h := ML2Spine.spineNu_le_step_bound (β := β) (gain := gain) (dens := dens) hϖ hε₁
    have : ML2Spine.spineDiv ϖ ε₁ ^ 2 * β * ML2Spine.spineRung β ϖ ε₁ gain dens 1
        ≤ ML2Spine.spineDiv ϖ ε₁ ^ 2 * ML2Spine.spineRung β ϖ ε₁ gain dens 1 := by
      have he2 : 0 ≤ ML2Spine.spineDiv ϖ ε₁ ^ 2 := by positivity
      nlinarith [mul_nonneg he2 hτ₁.le]
    linarith
  -- the dimensional constants
  set n := Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) with hn
  have hCv : (0 : ℝ) ≤ (Tube.volume_le.C n : ℝ) := NNReal.coe_nonneg _
  have hcv : (0 : ℝ) < (Tube.le_volume.c n : ℝ) := by exact_mod_cast Tube.le_volume.c_pos n
  -- the threshold
  obtain ⟨ρ₀, hρ₀, -, hthr⟩ := ML2Reduction.exists_threshold_const_le_rpow
    (A := C₀ ^ 2 * (Cu₀ : ℝ) * (Tube.volume_le.C n : ℝ) / (κ * (Tube.le_volume.c n : ℝ)))
    (g := ML2Spine.spineDiv ϖ ε₁ ^ 2 * ML2Spine.spineRung β ϖ ε₁ gain dens 1 / 2) (by positivity)
  have hρ₀' : (0 : NNReal) < ⟨ρ₀, hρ₀.le⟩ := by exact_mod_cast hρ₀
  filter_upwards [Ioc_mem_nhdsGT hρ₀', Ioo_mem_nhdsGT (zero_lt_one' NNReal)] with δ hδ hδ1
  intro Cu hCu Cstar hCstar a b m hab hbN hsep η' hcap p hap m' hm'lo hpm'
  have hδ0 : 0 < δ := hδ.1
  have hδr : (0 : ℝ) < (δ : ℝ) := hδ0
  have hδr1 : (δ : ℝ) < 1 := by exact_mod_cast hδ1.2
  have hδρ₀ : (δ : ℝ) ≤ ρ₀ := by exact_mod_cast hδ.2
  have hN : 0 < Tube.ssfGridLen δ := (Nat.zero_lt_of_lt hab).trans_le hbN
  -- `Θ ≥ δ^{-e²}` and `Θ_p ≤ Θ`
  have hΘ := ratio_ge_of_ceil_window hδ0 hδ1.2 hN he.le hsep hm'lo
  have hρm : (0 : ℝ) < (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ) := by
    exact_mod_cast gridScale_pos hδ0 _ _
  have hρp : (0 : ℝ) < (Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ) := by
    exact_mod_cast gridScale_pos hδ0 _ _
  have hρpa : (Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ)
      ≤ (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ) := by
    exact_mod_cast gridScale_antitone hδ0 hδr1.le _ hap
  have hΘp : (Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ)
        / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ)
      ≤ (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
        / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ) :=
    div_le_div_of_nonneg_right hρpa hρm.le
  -- `Cstar` is finite and its real value is `≤ δ^{-ν/20}`
  have hδpow_ne_top : ∀ y : ℝ, (δ : ENNReal) ^ y ≠ ⊤ := fun y => by
    rw [← ENNReal.coe_rpow_of_ne_zero hδ0.ne']; exact ENNReal.coe_ne_top
  have hCtop : Cstar ≠ ⊤ := ne_top_of_le_ne_top (hδpow_ne_top _) hCstar
  have hCs : Cstar.toReal ≤ (δ : ℝ) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens / 20)) := by
    have h := ENNReal.toReal_mono (hδpow_ne_top _) hCstar
    rwa [← ENNReal.toReal_rpow, ENNReal.coe_toReal] at h
  -- the real closure
  have hη'2 : 2 * η'
      ≤ ML2Spine.spineDiv ϖ ε₁ ^ 2 * ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1) / 32 := by
    linarith
  have hCu' : (Cu : ℝ) ≤ (Cu₀ : ℝ) := by exact_mod_cast hCu
  have hreal := floor_exponent_closes_real (η' := η') (Cu₀ := (Cu₀ : ℝ)) hδr hδr1 he hτ₁
    (ML2Spine.spineRung_one_le_spineRung_succ hβ0 hβ1 hϖ hε₁ hgain hdens m) hν0.le hνle
    hη'2 hκ hC₀ ENNReal.toReal_nonneg hCs (NNReal.coe_nonneg Cu)
    hCu' hCv hcv hΘ (div_nonneg hρp.le hρm.le) hΘp
    (hthr (δ : ℝ) hδr hδρ₀)
  -- back to `ℝ≥0∞`
  have hLtop : ENNReal.ofReal (((Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ)
        / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ))
        ^ (4 * (ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1) / 16)))
      * (Cstar ^ 2 * ENNReal.ofReal (C₀ ^ 2) * (Cu : ENNReal) * (δ : ENNReal) ^ (-(2 * η'))
        * ((Tube.volume_le.C n : NNReal) : ENNReal)) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top hCtop) ENNReal.ofReal_ne_top)
        ENNReal.coe_ne_top) (hδpow_ne_top _)) ENNReal.coe_ne_top)
  have hRtop : ENNReal.ofReal (((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
        / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ))
        ^ ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1))
      * ENNReal.ofReal κ * ((Tube.le_volume.c n : NNReal) : ENNReal) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      ENNReal.coe_ne_top
  rw [← ENNReal.toReal_le_toReal hLtop hRtop]
  have e1 := ENNReal.toReal_ofReal (Real.rpow_nonneg (div_nonneg hρp.le hρm.le)
    (4 * (ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1) / 16)))
  have e2 := ENNReal.toReal_ofReal (sq_nonneg C₀)
  have hρa : (0 : ℝ) < (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ) := by
    exact_mod_cast gridScale_pos hδ0 _ _
  have e3 := ENNReal.toReal_ofReal (Real.rpow_nonneg
    (div_nonneg hρa.le hρm.le) (ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1)))
  have e4 := ENNReal.toReal_ofReal hκ.le
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.coe_toReal, e1, e2, e3, e4,
    ← ENNReal.toReal_rpow]
  linarith [hreal]

/-! ### F4a — the count floor from the fill -/

open scoped Classical in
/-- **Alternative (F)'s count floor from the window twin and the fill**.

The binders are the source's own inputs, named rather than assumed: `hwin` is the twin (H1) —
survival at `τ` on the current hierarchy; `hCstar`/`hcap` are H2, closed by
`Kakeya.ML2Spine.floor_margin_H2`; the hierarchy is the trial's own (H3, condition `C-D1`); `hgap`
is the factor-4 scale gap H4 that `Kakeya.MultiScaleSubmult.maxDensity_le_two_fibreDeltaMax` needs
and `lemtwoscalemaxdensity` does not; `hfill` is **H5′**, the geometric core in its fill form: at the genuine parent the maximal density of the level-`m'` cells
inside a `p`-cell is attained, up to `κ`, on the cell itself.  H5′ is the *only* clause with no
producer in the tree; it is the source's "the first scale at which the transverse factor becomes
small determines a genuine parent `p`" (l.4135-4136), whose producer is the descent of
  `hclose` is **the exponent closure** (refined l.4145-4147, *"the first factor is
at least `(ρ_p/ρ_m)^{4ζ}` after decreasing `δ_f`"*), named rather than bought with an opaque
`δ ≤ δ₀` for the same reason `hCstar` and `hgap` are: all three are threshold-facts, and the
threshold is spent once, at the assembly; `floor_exponent_closes` (F6(iv)) discharges it below
`δ₀(β, ϖ, ε₁, gain, dens, κ, Cu₀, C₀)`.  `C₀` is the named `twoScaleConst` (C-F4d); one `κ` serves
`hfill` and `hclose` (C-F4e).

**C-F4f**: the eight binders `hβ0 hβ1 hϖ hε₁ hgain hdens hη' hcap` are carried
**for the call site** and are not consumed by this proof — they are exactly the inputs of F6(iv)
`floor_exponent_closes`, so the assembly discharges `hclose` with the very parameters it passes here,
and F4a and F6(iv) cannot drift apart. -/
theorem floor_of_windowLevels_of_fill
    {β ϖ ε₁ η' κ : ℝ} {gain dens : ℝ → ℝ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    (hη' : 0 < η') (hκ : 0 < κ)
    {ι : Type u} {δ Cu : NNReal} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    {u : Finset ι} {T : ι → Tube δ (EuclideanSpace ℝ (Fin 3))}
    (𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu)
    (hs : u.Nonempty)
    (hball : ∀ i ∈ u, (T i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)
    {Cstar : ENNReal} {a b m : ℕ}
    (hwin : ML2Reduction.IsKatzTaoDividingWindowLevels 𝒰 Cstar
      (ML2Spine.spineRung β ϖ ε₁ gain dens) (ML2Spine.spineDiv ϖ ε₁)
      (ML2Spine.spineCount ϖ ε₁) a b m)
    (hCstar : Cstar ≤ (δ : ENNReal) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens / 20)))
    (hcap : η' ≤ ML2Spine.spineDiv ϖ ε₁ ^ 2
      * ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1) / 64)
    (hgap : ∀ p c : ℕ, a ≤ p → p < c → c ≤ b →
      4 * (Tube.gridScale δ (Tube.ssfGridLen δ) c : ℝ)
        ≤ (Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ))
    {p : ℕ} (hap : a ≤ p) (hpar : ParentAdmissible 𝒰 η' a p)
    (hfill : ∀ jθ ∈ 𝒰.cover.indexSet a, ∀ jp ∈ 𝒰.nodesUnder p a jθ, ∀ m' : ℕ, p < m' → m' ≤ b →
      FillAt 𝒰 κ p m' jp)
    (hclose : ∀ m' : ℕ, a + ⌈ML2Spine.spineDiv ϖ ε₁ * ((b : ℝ) - (a : ℝ))⌉₊ ≤ m' → p < m' →
      m' ≤ b →
      ENNReal.ofReal (((Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ)
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
            : ENNReal)) :
    ∀ jθ ∈ 𝒰.cover.indexSet a, ∀ jp ∈ 𝒰.nodesUnder p a jθ, ∀ m' : ℕ, a < m' → m' < b →
      ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
          / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) ^ (1 - ML2Spine.spineDiv ϖ ε₁)
        ≤ (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
          / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ) →
      (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
          / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ)
        ≤ ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
          / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) ^ ML2Spine.spineDiv ϖ ε₁ →
      p < m' →
      ((Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ)
          / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ))
            ^ (2 + 4 * (ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1) / 16))
        ≤ ((𝒰.nodesUnder m' p jp).card : ℝ) := by
  intro jθ hjθ jp hjp m' ham' hm'b hlo hhi hpm'
  have hδ1' : δ ≤ 1 := hδ1.le
  have hN : 0 < Tube.ssfGridLen δ :=
    (Nat.zero_lt_of_lt hwin.coarse_lt_fine).trans_le hwin.fine_le_gridLen
  have hm'N : m' ≤ Tube.ssfGridLen δ := hm'b.le.trans hwin.fine_le_gridLen
  obtain ⟨hwlo, hwhi⟩ := ceil_window_of_ratio hδ0 hδ1 hN ham' hm'b hlo hhi
  have hjp_idx : jp ∈ 𝒰.cover.indexSet p := by
    have h := hjp
    simp only [Tube.UniformTubeSet.nodesUnder, Tube.UniformTubeSet.nodesIn,
      Finset.mem_filter] at h
    exact h.1
  have hδpow_ne_top : ∀ y : ℝ, (δ : ENNReal) ^ y ≠ ⊤ := fun y => by
    rw [← ENNReal.coe_rpow_of_ne_zero hδ0.ne']; exact ENNReal.coe_ne_top
  have hCtop : Cstar ≠ ⊤ := ne_top_of_le_ne_top (hδpow_ne_top _) hCstar
  have hgap4 : 4 * Tube.gridScale δ (Tube.ssfGridLen δ) m'
      ≤ Tube.gridScale δ (Tube.ssfGridLen δ) p := by
    have := hgap p m' hap hpm' hm'b.le
    exact_mod_cast this
  -- the chain W1 → F1 → F1b → F3, at the given cell
  have hchain := ofReal_ratio_le_maxDensity_nodesUnder_parent hδ0 hδ1' 𝒰 hs hball hwin hCtop hap
    hpar hpm'.le hm'N hgap4 hwlo hwhi hjθ hjp_idx
  -- the fill, and the two tube volumes
  have hfillp := hfill jθ hjθ jp hjp m' hpm' hm'b.le
  unfold FillAt at hfillp
  set n := Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) with hn_def
  have hn : n = 3 := finrank_euclideanSpace_fin
  have hn1 : n - 1 = 2 := by rw [hn]
  have hall : ∀ j' ∈ 𝒰.nodesUnder m' p jp,
      (𝒰.cover.tube m' j').toConvexSpaceBody ≤ (𝒰.cover.tube p jp).toConvexSpaceBody := by
    intro j' hj'
    have h := hj'
    simp only [Tube.UniformTubeSet.nodesUnder, Tube.UniformTubeSet.nodesIn,
      Finset.mem_filter] at h
    exact h.2
  have hsum := Kakeya.sum_volume_eq_densityIn_mul_volume'
    (s := 𝒰.nodesUnder m' p jp) (W := fun j' => (𝒰.cover.tube m' j').toConvexSpaceBody) hall
  have hsumle : ∑ j' ∈ 𝒰.nodesUnder m' p jp, volume ((𝒰.cover.tube m' j').toConvexSpaceBody).carrier
      ≤ ((𝒰.nodesUnder m' p jp).card : ENNReal)
        * (((Tube.volume_le.C n : NNReal) : ENNReal)
          * ((Tube.gridScale δ (Tube.ssfGridLen δ) m' : NNReal) : ENNReal) ^ (n - 1)) := by
    rw [← nsmul_eq_mul]
    exact Finset.sum_le_card_nsmul _ _ _
      (fun j' _ => Tube.volume_le (gridScale_le_one hδ1' _ _) (𝒰.cover.tube m' j'))
  have hUlo : ((Tube.le_volume.c n : NNReal) : ENNReal)
        * ((Tube.gridScale δ (Tube.ssfGridLen δ) p : NNReal) : ENNReal) ^ (n - 1)
      ≤ volume ((𝒰.cover.tube p jp).toConvexSpaceBody).carrier :=
    Tube.le_volume (𝒰.cover.tube p jp)
  -- `κ · Δ_p · c_vol ρ_p² ≤ Δ(·,T_p)·|T_p| = Σ|V| ≤ #cells · C_vol ρ_{m'}²`
  have hkey : ENNReal.ofReal κ
        * Kakeya.maxDensity (𝒰.nodesUnder m' p jp)
            (fun j' => (𝒰.cover.tube m' j').toConvexSpaceBody)
        * (((Tube.le_volume.c n : NNReal) : ENNReal)
          * ((Tube.gridScale δ (Tube.ssfGridLen δ) p : NNReal) : ENNReal) ^ (n - 1))
      ≤ ((𝒰.nodesUnder m' p jp).card : ENNReal)
        * (((Tube.volume_le.C n : NNReal) : ENNReal)
          * ((Tube.gridScale δ (Tube.ssfGridLen δ) m' : NNReal) : ENNReal) ^ (n - 1)) :=
    (mul_le_mul' hfillp hUlo).trans ((le_of_eq hsum.symm).trans hsumle)
  -- the closure, with `C₀²` as the square of `ofReal C₀`
  have hcl := hclose m' hwlo hpm' hm'b.le
  rw [ENNReal.ofReal_pow (twoScaleConst_pos.{u, 0} (EuclideanSpace ℝ (Fin 3))).le] at hcl
  -- name the pieces
  set L := ENNReal.ofReal (((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
    / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ)) ^ ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1))
    with hL
  set A := ENNReal.ofReal (((Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ)
    / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ))
    ^ (4 * (ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1) / 16))) with hA
  set Δp := Kakeya.maxDensity (𝒰.nodesUnder m' p jp)
    (fun j' => (𝒰.cover.tube m' j').toConvexSpaceBody) with hΔp
  set X' := Cstar ^ 2 * ENNReal.ofReal (twoScaleConst.{u, 0} (EuclideanSpace ℝ (Fin 3))) ^ 2
    * (Cu : ENNReal) * (δ : ENNReal) ^ (-(2 * η')) with hX'
  set Cv : ENNReal := ((Tube.volume_le.C n : NNReal) : ENNReal) with hCv
  set cv : ENNReal := ((Tube.le_volume.c n : NNReal) : ENNReal) with hcv
  set ρp : ENNReal := ((Tube.gridScale δ (Tube.ssfGridLen δ) p : NNReal) : ENNReal) with hρp
  set ρm : ENNReal := ((Tube.gridScale δ (Tube.ssfGridLen δ) m' : NNReal) : ENNReal) with hρm
  set K : ENNReal := ((𝒰.nodesUnder m' p jp).card : ENNReal) with hK
  -- `L > 0`, hence `Cstar ≠ 0` and `Cu ≠ 0`
  have hρmr : (0 : ℝ) < (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ) := by
    exact_mod_cast gridScale_pos hδ0 _ _
  have hρpr : (0 : ℝ) < (Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ) := by
    exact_mod_cast gridScale_pos hδ0 _ _
  have hρar : (0 : ℝ) < (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ) := by
    exact_mod_cast gridScale_pos hδ0 _ _
  have hLpos : 0 < L := ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (div_pos hρar hρmr) _)
  have hX'0 : X' ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hchain
    exact hLpos.ne' (le_antisymm hchain bot_le)
  have hX'top : X' ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top hCtop)
      (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)) ENNReal.coe_ne_top) (hδpow_ne_top _)
  have hCv0 : Cv ≠ 0 := by
    rw [hCv, Ne, ENNReal.coe_eq_zero]; exact (Tube.volume_le.C_pos n).ne'
  have hX0 : X' * Cv ≠ 0 := mul_ne_zero hX'0 hCv0
  have hXtop : X' * Cv ≠ ⊤ := ENNReal.mul_ne_top hX'top ENNReal.coe_ne_top
  -- assemble:
  -- `A · X' · Cv · ρ_p^{n-1} ≤ L κ cv ρ_p^{n-1} ≤ X' (κ Δ_p cv ρ_p^{n-1}) ≤ X' K Cv ρ_m^{n-1}`
  have hmain : A * ρp ^ (n - 1) * (X' * Cv) ≤ K * ρm ^ (n - 1) * (X' * Cv) := by
    calc A * ρp ^ (n - 1) * (X' * Cv) = A * (X' * Cv) * ρp ^ (n - 1) := by ring
      _ ≤ L * ENNReal.ofReal κ * cv * ρp ^ (n - 1) := mul_le_mul' hcl le_rfl
      _ = L * (ENNReal.ofReal κ * (cv * ρp ^ (n - 1))) := by ring
      _ ≤ X' * Δp * (ENNReal.ofReal κ * (cv * ρp ^ (n - 1))) := mul_le_mul' hchain le_rfl
      _ = X' * (ENNReal.ofReal κ * Δp * (cv * ρp ^ (n - 1))) := by ring
      _ ≤ X' * (K * (Cv * ρm ^ (n - 1))) := mul_le_mul' le_rfl hkey
      _ = K * ρm ^ (n - 1) * (X' * Cv) := by ring
  have hfin : A * ρp ^ (n - 1) ≤ K * ρm ^ (n - 1) :=
    (ENNReal.mul_le_mul_iff_left hX0 hXtop).mp hmain
  rw [hn1] at hfin
  -- to `ℝ`
  have hfin' := (ENNReal.toReal_le_toReal
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top))
    (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.pow_ne_top ENNReal.coe_ne_top))).mpr
    hfin
  have eA := ENNReal.toReal_ofReal (Real.rpow_nonneg (div_nonneg hρpr.le hρmr.le)
    (4 * (ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1) / 16)))
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.coe_toReal,
    ENNReal.toReal_natCast, eA] at hfin'
  -- `Θ_p^{2+4ζ} = Θ_p² · Θ_p^{4ζ}`
  have hΘp0 : (0 : ℝ) < (Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ)
      / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ) := div_pos hρpr hρmr
  rw [Real.rpow_add hΘp0, Real.rpow_two, div_pow, div_mul_eq_mul_div,
    div_le_iff₀ (by positivity)]
  nlinarith [hfin']

end Kakeya.ML2Core

end

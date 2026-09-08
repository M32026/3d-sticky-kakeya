/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.BallGrid
public import Kakeya.DimensionThree.Plank.BoxDensityTransfer
public import Kakeya.DimensionThree.Plank.DenseBox

/-!
# Dense `θb`-ball capture, and the bridge from the per-box dense-box estimate

This file joins the two halves of the paper's local route for item 1 of GWZ Lemma 6.13.

The first half is already proved, but only as an anonymous intermediate step: inside
`Plank.perRepresentativeDensity_saturated_dilated` there is a `have` establishing, for a single
shifted grid box `B_q`, the equation-(37) estimate

`cDense · cLam · a ^ (2η) · lam · |B_q| ≤ |U ∩ B_q|`,

a lower bound on the *union* inside the box.  `Plank.denseBoxUnionEstimate_shiftedBox` below states
it as a public lemma.  This is the estimate that makes item 1 work at all: it is obtained by
Cauchy–Schwarz against the angular-concentration hypothesis, i.e. by controlling the `L²` norm of
the multiplicity function, and it therefore needs no upper bound on the multiplicity — which the
hypotheses of Lemma 6.13 do not provide.

The second half is `Plank.denseBallUnionCapture_of_denseBox`.  A shifted grid box is a genuine
`Plank.ThetaBox θ b`, so its `θb`-ball grid has total volume at most `729 · |B_q|` with an absolute
constant, and the non-dense balls can be charged against `|B_q|` rather than against a sum of
shading masses.

`Plank.denseBallCapture_of_denseBoxEstimate` composes them at the ball threshold `cThr · lowQ`,
where `cThr = (2 · Cball)⁻¹` is absolute and is fixed before the box and the configuration.  It is
the form item 1 consumes: every point of the retained local union lies in a `θb`-ball that is dense
for the retained set itself, which is exactly the `hcover` hypothesis of
`Plank.denseBall_arbitraryCentre_fullness`.  Only `lowQ` carries configuration dependence and it
enters linearly, so a dense-box estimate at `lowQ = cBox · a ^ E` gives a ball density at
`cThr · cBox · a ^ E` with no further loss.
-/

@[expose] public section

open MeasureTheory Convexity
open scoped NNReal Real ENNReal

noncomputable section

namespace Plank

variable {ι : Type*}

/-! ## Dense `θb`-ball capture inside a single dense box

This section carries the local half of item 1 of GWZ Lemma 6.13, and it is the step that makes the
whole item work without any upper bound on the multiplicity.

The global "delete the sparse `θb`-balls" argument fails: its cost is `t · B_tot`, where `B_tot` is
the total volume of a `θb`-ball cover of the *whole* shading union, and nothing in the hypotheses of
Lemma 6.13 compares `B_tot` with `|U|` — doing so amounts to an upper bound on the average
multiplicity, which the hypotheses bound only from below.

Run inside one box, the same argument costs nothing extra.  `Plank.thetaBallGrid_sum_volume_le`
bounds the total grid volume by `729 · |Q|` with an **absolute** constant, and the dense-box
estimate `Plank.denseBoxEstimate_boxNormalised_combined` bounds the local union from below
by `lowQ · |Q|` (this is equation (37) of the paper; note it is a genuine *union* bound, obtained by
Cauchy–Schwarz against the angular-concentration hypothesis, not a sum-of-shades bound).  So the
deleted mass is at most `t · 729 · |Q| ≤ (729 t / lowQ) · |U_Q|`, and choosing `t` a fixed fraction
of `lowQ / 729` retains half of `|U_Q|`.  The retention constant is the absolute `1/2`; the whole
configuration dependence sits in `lowQ`, where the paper puts it.

`Plank.denseBallUnionCapture_of_denseBox` packages this.  Its last conclusion is stated for the
*retained* set `UQ ∩ GQ` rather than for `UQ`, which is what
`Plank.denseBall_arbitraryCentre_fullness` consumes: a dense ball is contained in `GQ`, so cutting
`UQ` down to `UQ ∩ GQ` does not change its intersection with that ball.
-/

/-- **Dense `θb`-balls inside a dense box capture half of the local union.**

`UQ` is any measurable subset of the box `Q` (the intended instance is the local shading union of
the planks assigned to the slab, restricted to `Q`), and `Cball` bounds the total grid volume by
`Cball · |Q|` (`Plank.thetaBallGrid_sum_volume_le`, with the absolute value `729`).

Provided the ball threshold `t` satisfies `2 · t · Cball · |Q| ≤ |UQ|` — which is exactly what the
dense-box estimate `lowQ · |Q| ≤ |UQ|` supplies once `t := lowQ / (2 · Cball)` — the union `GQ` of
the dense grid
balls retains half of `UQ`, and every point of `GQ` lies in a grid ball that is dense *for the
retained set* `UQ ∩ GQ`.

The density clause is quantified over `GQ`, not over `UQ ∩ GQ`.  That matters downstream: when the
local sets are aggregated over many boxes and slabs, a point of the global retained shading may lie
in the `GQ` of a box whose own local union it does not belong to, and it still has to be handed a
dense ball.  Nothing is lost, because the proof only ever uses that `y` lies in some dense grid
ball.

The retention constant is the absolute `1/2`: no power of `a` and no configuration datum enters it.
The non-dense balls are charged against `|Q|`, never against a sum of shading masses, which is
exactly what keeps the estimate free of any multiplicity hypothesis. -/
theorem denseBallUnionCapture_of_denseBox {theta b : ℝ≥0} {htheta1 : theta ≤ 1}
    (Q : ThetaBox theta b htheta1) (htheta : 0 < theta) (hb : 0 < b)
    (UQ : Set (EuclideanSpace ℝ (Fin 3)))
    (hUQ : UQ ⊆ (Q.carrier : Set (EuclideanSpace ℝ (Fin 3))))
    (hUQtop : volume UQ ≠ ⊤)
    (Cball t : ENNReal)
    (hCball : ∀ 𝒞 : ThetaBallGrid, IsThetaBallGridFor Q 𝒞 →
      ∑ c ∈ 𝒞, volume (thetaBall theta b c) ≤ Cball * volume Q.carrier)
    (ht : 2 * (t * (Cball * volume Q.carrier)) ≤ volume UQ) :
    ∃ GQ : Set (EuclideanSpace ℝ (Fin 3)), MeasurableSet GQ ∧
      volume UQ ≤ 2 * volume (UQ ∩ GQ) ∧
      (∀ y ∈ GQ, ∃ c : EuclideanSpace ℝ (Fin 3),
        y ∈ thetaBall theta b c ∧
        t * volume (thetaBall theta b c)
          ≤ volume ((UQ ∩ GQ) ∩ thetaBall theta b c)) := by
  obtain ⟨L⟩ := exists_denseBallLayer Q htheta hb UQ hUQ t
  set GQ : Set (EuclideanSpace ℝ (Fin 3)) := ⋃ c ∈ L.denseBalls, thetaBall theta b c with hGQ
  have hmeas : MeasurableSet GQ := by
    rw [hGQ]
    exact Finset.measurableSet_biUnion _ (fun c _ => measurableSet_closedBall)
  set u : ENNReal := volume UQ with hu
  set g : ENNReal := volume (UQ ∩ GQ) with hg
  set m : ENNReal := t * ∑ c ∈ L.grid, volume (thetaBall theta b c) with hm
  have hUQtop' : u ≠ ⊤ := by
    simpa [hu] using hUQtop
  have hsum_le : (∑ c ∈ L.grid, volume (thetaBall theta b c)) ≤ Cball * volume Q.carrier :=
    hCball L.grid L.grid_ok
  have hm_le : m ≤ t * (Cball * volume Q.carrier) := by
    dsimp [m]
    exact mul_le_mul_right hsum_le t
  have h2m_le_u : 2 * m ≤ u := by
    calc
      2 * m ≤ 2 * (t * (Cball * volume Q.carrier)) := by
        exact mul_le_mul_right hm_le 2
      _ ≤ volume UQ := ht
      _ = u := by rw [hu]
  have hmass : u ≤ g + m := by
    simpa [hu, hg, hm, hGQ] using L.mass_captured
  have hu_le_2g : u ≤ 2 * g := by
    have h1 : 2 * u ≤ 2 * g + 2 * m := by
      calc
        2 * u ≤ 2 * (g + m) := by exact mul_le_mul_right hmass 2
        _ = 2 * g + 2 * m := by rw [mul_add]
    have h2 : 2 * g + 2 * m ≤ 2 * g + u := by
      exact add_le_add_right h2m_le_u (2 * g)
    have h3 : 2 * u ≤ 2 * g + u := le_trans h1 h2
    have h3' : u + u ≤ 2 * g + u := by
      simpa [two_mul] using h3
    exact (ENNReal.add_le_add_iff_right hUQtop').mp h3'
  refine ⟨GQ, hmeas, hu_le_2g, ?_⟩
  intro y hyGQ
  have hyGQ' : y ∈ ⋃ c ∈ L.denseBalls, thetaBall theta b c := by
    simpa [hGQ] using hyGQ
  obtain ⟨c, hc, hyc⟩ := Set.mem_iUnion₂.mp hyGQ'
  refine ⟨c, hyc, ?_⟩
  have hball_sub : thetaBall theta b c ⊆ GQ := by
    intro x hx
    rw [hGQ]
    exact Set.mem_iUnion₂.mpr ⟨c, hc, hx⟩
  have heq : (UQ ∩ GQ) ∩ thetaBall theta b c = UQ ∩ thetaBall theta b c := by
    ext x
    constructor
    · intro hx
      exact ⟨hx.1.1, hx.2⟩
    · intro hx
      exact ⟨⟨hx.1, hball_sub hx.2⟩, hx.2⟩
  rw [heq]
  exact L.isDense c hc

/-! ## From the per-box dense-box estimate to dense `θb`-balls -/

/-- **The per-box dense-box estimate, on one shifted grid box** (equation (37)).

This is the single-box slice of the `hdense` step inside
`Plank.perRepresentativeDensity_saturated_dilated`, stated publicly.  The conclusion is a lower
bound on the measure of the *union* of the shadings inside the box, not on a sum of shadings and
not on a fullness. -/
theorem denseBoxUnionEstimate_shiftedBox (cTan Ceta : ℝ≥0) (hCeta : 0 < Ceta) :
    ∃ cDense : ℝ≥0, 0 < cDense ∧
      ∀ {a b θ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {hθ1 : θ ≤ 1} {ι : Type*}
        (s : Finset ι) (V : ι → Plank a b hab hb1)
        (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
        (S : Slab θ hθ1) (t : Fin 3 → ℝ) (q : Fin 3 → ℤ)
        (Tq : Finset ι) (Z : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
        (η : ℝ) (θ0 : ℝ) (Mtyp Cstar cLam lam : ℝ≥0),
        0 < a → 0 < b → 0 < θ → 0 < η → 0 < cLam → a / b ≤ θ →
        ((a / b : ℝ≥0) : ℝ) ≤ θ0 → θ0 ≤ 1 → (θ : ℝ) ≤ (Cstar : ℝ) * θ0 →
        (Cstar : ENNReal) * (Mtyp : ENNReal) ≤ (Ceta : ENNReal) * (a : ENNReal) ^ (-η) →
        cLam * a ^ η ≤ lam →
        Tq ⊆ s →
        (∀ i ∈ s, (Y i).shade ⊆ ((V i).carrier : Set (EuclideanSpace ℝ (Fin 3)))) →
        (∀ i ∈ Tq, (Z i).shade ⊆ (Y i).shade ∩
          ((shiftedSlabBox S b t q).carrier : Set (EuclideanSpace ℝ (Fin 3)))) →
        (∀ i ∈ Tq, (Z i).carrier = (V i).carrier) →
        (∀ i ∈ Tq, Kakeya.ComparableScalars cTan
          (volume (((V i).carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩
            (shiftedSlabBox S b t q).carrier)).toNNReal (a * b ^ 2)) →
        b * lam ≤ ShadedBody.fullness Tq Z →
        ((∑ i ∈ Tq, ∑ j ∈ Tq, volume ((Z i).shade ∩ (Z j).shade))
          ≤ (Mtyp : ENNReal) * (∑ i ∈ Tq, ∑ j ∈ Tq with
              (θ0 - ((a / b : ℝ≥0) : ℝ) ≤ Prism3D.angle (V i) (V j) ∧
                Prism3D.angle (V i) (V j) ≤ 2 * θ0),
            volume ((Z i).shade ∩ (Z j).shade))) →
        ((cDense * cLam * a ^ (2 * η) * lam : ℝ≥0) : ENNReal) *
            volume ((shiftedSlabBox S b t q).carrier)
          ≤ volume ((⋃ i ∈ s, (Y i).shade) ∩
              ((shiftedSlabBox S b t q).carrier : Set (EuclideanSpace ℝ (Fin 3)))) := by
  obtain ⟨cDense, hcDense, hdensebox⟩ := denseBoxEstimate_boxNormalised_combined cTan Ceta hCeta
  refine ⟨cDense, hcDense, ?_⟩
  intro a b θ hab hb1 hθ1 ι s V Y S t q Tq Z η θ0 Mtyp Cstar cLam lam ha hb hθ hη hcLam habθ
    habθ0 hθ01 hθθ0 hMtyp_combined hlam_lb hTsub hsh hZsh hZcar htan hlam hconc
  have hlam_pos : 0 < lam :=
    lt_of_lt_of_le (mul_pos hcLam (NNReal.rpow_pos ha)) hlam_lb
  have hblam_pos : 0 < b * lam := mul_pos hb hlam_pos
  have hne : Tq.Nonempty :=
    nonempty_of_pos_le_fullness Tq Z hblam_pos hlam
  have hshq : ∀ i ∈ Tq, (Z i).shade
      ⊆ ((V i).carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩
        ((shiftedSlabBox S b t q).carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
    intro i hi
    refine (hZsh i hi).trans ?_
    exact Set.inter_subset_inter_left _ (hsh i (hTsub hi))
  have hkey := hdensebox Tq V Z θ hθ1 (shiftedSlabBox S b t q) η θ0 Mtyp Cstar cLam lam ha hb hη
    habθ hne hshq htan hZcar habθ0 hθ01 hθθ0
    hMtyp_combined hlam_lb hlam hconc
  refine le_trans hkey (measure_mono ?_)
  refine Set.iUnion₂_subset fun i hi => ?_
  intro x hx
  have hx' := hZsh i hi hx
  obtain ⟨hxY, hxB⟩ := hx'
  exact ⟨Set.mem_biUnion (hTsub hi) hxY, hxB⟩

/-- **Dense `θb`-balls from a dense-box estimate.**

`Plank.denseBallUnionCapture_of_denseBox` run at the grid-volume constant of
`Plank.thetaBallGrid_sum_volume_le` and at the ball threshold `cThr · lowQ`, where
`cThr = (2 · Cball)⁻¹` is absolute and is fixed **before** the box and the configuration.  The
hypothesis `2 · t · Cball · |Q| ≤ |U ∩ Q|` of that theorem is then exactly the dense-box estimate
`lowQ · |Q| ≤ |U ∩ Q|`.

The last clause is the `hcover` input of `Plank.denseBall_arbitraryCentre_fullness` for the local
union: the density is stated for the *retained* set, and the retention constant is the absolute
`1/2`.  Only `lowQ` carries configuration dependence, and it enters the ball threshold linearly —
so a dense-box estimate at `lowQ = cBox · a ^ E` yields a ball density at `cThr · cBox · a ^ E`,
with no further loss. -/
theorem denseBallCapture_of_denseBoxEstimate :
    ∃ cThr : ℝ≥0, 0 < cThr ∧
      ∀ {theta b : ℝ≥0} {htheta1 : theta ≤ 1}
        (Q : ThetaBox theta b htheta1), 0 < theta → 0 < b →
        ∀ (U : Set (EuclideanSpace ℝ (Fin 3))), MeasurableSet U →
        ∀ lowQ : ℝ≥0,
        (lowQ : ENNReal) * volume Q.carrier
          ≤ volume (U ∩ (Q.carrier : Set (EuclideanSpace ℝ (Fin 3)))) →
        ∃ GQ : Set (EuclideanSpace ℝ (Fin 3)), MeasurableSet GQ ∧
          volume (U ∩ (Q.carrier : Set (EuclideanSpace ℝ (Fin 3))))
            ≤ 2 * volume ((U ∩ (Q.carrier : Set (EuclideanSpace ℝ (Fin 3)))) ∩ GQ) ∧
          (∀ y ∈ GQ,
            ∃ c : EuclideanSpace ℝ (Fin 3),
              y ∈ thetaBall theta b c ∧
              ((cThr * lowQ : ℝ≥0) : ENNReal) * volume (thetaBall theta b c)
                ≤ volume (((U ∩ (Q.carrier : Set (EuclideanSpace ℝ (Fin 3)))) ∩ GQ)
                    ∩ thetaBall theta b c)) := by
  obtain ⟨Cball, hCballpos, hCball⟩ := thetaBallGrid_sum_volume_le
  refine ⟨(2 * Cball)⁻¹, ?_, ?_⟩
  · positivity
  · intro theta b htheta1 Q htheta hb U hUmeas lowQ hlow
    have hQcar_top : volume Q.carrier ≠ ⊤ := by
      exact Q.isCompact.measure_ne_top
    have hUQtop : volume (U ∩ (Q.carrier : Set (EuclideanSpace ℝ (Fin 3)))) ≠ ⊤ := by
      exact ne_top_of_le_ne_top hQcar_top
        (measure_mono (Set.inter_subset_right :
          (U ∩ (Q.carrier : Set (EuclideanSpace ℝ (Fin 3))))
            ⊆ (Q.carrier : Set (EuclideanSpace ℝ (Fin 3)))))
    have hCballE : ∀ 𝒞 : ThetaBallGrid, IsThetaBallGridFor Q 𝒞 →
        ∑ c ∈ 𝒞, volume (thetaBall theta b c) ≤ (Cball : ENNReal) * volume Q.carrier := by
      intro 𝒞 h𝒞
      exact hCball Q htheta hb 𝒞 h𝒞
    let t : ENNReal := (((2 * Cball)⁻¹ * lowQ : ℝ≥0) : ENNReal)
    have hscalar : (2 : ℝ≥0) * ((2 * Cball)⁻¹ * lowQ) * Cball = lowQ := by
      have hne : (2 * Cball : ℝ≥0) ≠ 0 := by positivity
      calc
        (2 : ℝ≥0) * ((2 * Cball)⁻¹ * lowQ) * Cball
            = (2 * Cball) * ((2 * Cball)⁻¹ * lowQ) := by ring
        _ = ((2 * Cball) * (2 * Cball)⁻¹) * lowQ := by ring
        _ = lowQ := by rw [mul_inv_cancel₀ hne, one_mul]
    have ht : (2 : ENNReal) * (t * ((Cball : ENNReal) * volume Q.carrier))
        ≤ volume (U ∩ (Q.carrier : Set (EuclideanSpace ℝ (Fin 3)))) := by
      calc
        (2 : ENNReal) * (t * ((Cball : ENNReal) * volume Q.carrier))
            = (((2 : ℝ≥0) * ((2 * Cball)⁻¹ * lowQ) * Cball : ℝ≥0) : ENNReal)
                * volume Q.carrier := by
              dsimp [t]
              simp [← ENNReal.coe_mul, mul_assoc, mul_comm, mul_left_comm]
        _ = (lowQ : ENNReal) * volume Q.carrier := by rw [hscalar]
        _ ≤ volume (U ∩ (Q.carrier : Set (EuclideanSpace ℝ (Fin 3)))) := hlow
    obtain ⟨GQ, hGQmeas, hret, hdens⟩ := denseBallUnionCapture_of_denseBox Q htheta hb
      (U ∩ (Q.carrier : Set (EuclideanSpace ℝ (Fin 3))))
      (Set.inter_subset_right :
        (U ∩ (Q.carrier : Set (EuclideanSpace ℝ (Fin 3))))
          ⊆ (Q.carrier : Set (EuclideanSpace ℝ (Fin 3))))
      hUQtop (Cball : ENNReal) t hCballE ht
    refine ⟨GQ, hGQmeas, hret, ?_⟩
    intro y hy
    obtain ⟨c, hc_mem, hc_dense⟩ := hdens y hy
    refine ⟨c, hc_mem, ?_⟩
    simpa [t] using hc_dense

end Plank

end

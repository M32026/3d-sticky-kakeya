/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.GridRounding
public import Kakeya.DimensionThree.MainLemma2.NonSlabFibre

/-!
# Moving the scale-`r` layer of Main Lemma 2 onto the multiscale grid

Configuration `hyp:ml2setup` supplies a uniform family only on the grid of GWZ Definition 2.1,
whose scales are the `δ^{k/N}` with `N = ⌈log log 1/δ⌉`, while the scale-`r` interface is
invoked at an arbitrary radius `r ≥ a` — at `r = θ b` in the transverse branch, a radius
nothing makes of that form. This file contains the *proved* material that bridges the two, so
that the only assumptions left in
`Kakeya.DimensionThree.MainLemma2.AScaleInterface` are the ones owned by Sections 3 and 5.

The bridge is a rounding, and it is elementary:
`Kakeya.VeryNotSticky.exists_gridIndex` rounds `r` up to the nearest grid scale `ρ`, and
`Kakeya.VeryNotSticky.gridStep_le` says the resulting `ρ / r` is at most `δ^{-η}`, which is the
configuration's field `Kakeya.VeryNotSticky.gridFine`. Nothing here needs `r` to be a grid
scale, and nothing here is asserted rather than proved.

What the rounding costs, conjunct by conjunct — this is the point, and the previous docstrings
of the interface had it wrong:

* the **tube-volume comparison** costs *nothing*. Rounding *up* makes the parent radius `ρ`
  at least `r`, and the comparison
  `c₃/C₃ · r² |T| ≤ δ² |T_ρ|` is monotone in the parent radius, so it is free
  (`Kakeya.tubeVolumeRatio_of_le`). The belief that it pulls against the multiplicity bound —
  "one wants parent radius `≤ r`, the other `≥ r`" — came from reading it at a parent radius
  *below* `r`; at the rounded radius both are read at the same `ρ`, and only one of them pays.
* the **two-scale multiplicity bound** costs `(ρ/r)² ≤ δ^{-2η}`, and that is charged to the
  gain, not to a constant: the parent multiplicity is taken to be `δ^{ν/45} Δ_max(𝕋_ρ) δ^η`
  rather than `Δ_max(𝕋_ρ) δ^η`, which absorbs the loss because `ν ≥ 90 η`
  (`Kakeya.VeryNotSticky.rpow_mul_sq_le_sq_of_gridStep`).
* the **ball estimate** costs the ratio of ball volumes `(ρ/r)³ ≤ δ^{-3η}`, charged to the
  factor `δ^{ν/9}` that `Kakeya.VeryNotSticky.AScaleData` carries
  (`Kakeya.VeryNotSticky.rpow_mul_cube_le_cube_of_gridStep`). That same `δ^{ν/9}` also pays a
  further `δ^{η}`, the room the ball conjunct of
  `Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid` carries so that Section 5 can afford
  the factor `C₀` of the overlap substitution; with it the requirement is `ν/9 - η ≥ 3η`, i.e.
  `ν ≥ 36 η` (`Kakeya.VeryNotSticky.rpow_sub_eta_mul_cube_le_cube_of_gridStep`).

All charges are covered by `ν ≥ 90 η`, so no new threshold on the gain is introduced; the one
new hypothesis is the configuration's `gridFine`, a condition on `δ` alone.

One further piece of accounting lives here, `Kakeya.VeryNotSticky.coe_C₀_le_rpow_neg_eta`:
the configuration's branching/overlap constant satisfies `C₀ ≤ δ^{-η}`, because the clause
`aScaleData_absorb` absorbs a comparison constant that dominates `C₀`. That is what makes the
loss incurred by replacing pairwise essential distinctness with bounded overlap, in the two
statements of `Kakeya.DimensionThree.MainLemma2.AScaleResidues`, sub-polynomial rather than
arbitrary.
-/

@[expose] public section

namespace Kakeya

open MeasureTheory Metric Set

/-! ### The tube-volume comparison is monotone in the parent radius -/

/-- **Rounding the parent radius up leaves the tube-volume comparison free** (blueprint
`lem:ml2tubeVolumeRatio`, read at a parent radius above the nominal one).

If the reference tube volume `volT` is at most the dimensional upper bound `C₃ δ²` of
`Tube.volume_le`, and the parent radius `ρ` is at least the nominal radius `r`, then

`c · r² · volT ≤ δ² · (c₃ ρ²)`

with `c = Kakeya.tubeVolumeRatioConstant 3 = c₃ / C₃`, the right-hand side being the
dimensional *lower* bound of `Tube.le_volume` for the volume of a `ρ`-tube. The two
dimensional constants cancel exactly, and the hypothesis `r ≤ ρ` is used once and in the
harmless direction.

This is the conjunct of `Kakeya.VeryNotSticky.rScaleParentData_of_gridScale` that costs nothing
under rounding, and it is why the tube-volume comparison and the two-scale multiplicity bound
do *not* pull in opposite directions: read at the same rounded parent radius, only the second
one pays. -/
theorem tubeVolumeRatio_of_le {δ r ρ : NNReal} (hrρ : r ≤ ρ) {volT : ENNReal}
    (hvolT : volT ≤ (Tube.volume_le.C 3 : ENNReal) * (δ : ENNReal) ^ 2) :
    (tubeVolumeRatioConstant 3 : ENNReal) * ((r : ENNReal) ^ 2 * volT) ≤
      (δ : ENNReal) ^ 2 * ((Tube.le_volume.c 3 : ENNReal) * (ρ : ENNReal) ^ 2) := by
  have hC₃₀ : Tube.volume_le.C 3 ≠ 0 := ne_of_gt (Tube.volume_le.C_pos 3)
  have hc_mul : (tubeVolumeRatioConstant 3 : ENNReal) * (Tube.volume_le.C 3 : ENNReal) =
      (Tube.le_volume.c 3 : ENNReal) := by
    rw [tubeVolumeRatioConstant, ENNReal.coe_div hC₃₀]
    exact ENNReal.div_mul_cancel (by exact_mod_cast hC₃₀) (by simp)
  calc
    (tubeVolumeRatioConstant 3 : ENNReal) * ((r : ENNReal) ^ 2 * volT)
        ≤ (tubeVolumeRatioConstant 3 : ENNReal) *
            ((r : ENNReal) ^ 2 * ((Tube.volume_le.C 3 : ENNReal) * (δ : ENNReal) ^ 2)) := by
          gcongr
    _ = (tubeVolumeRatioConstant 3 : ENNReal) * (Tube.volume_le.C 3 : ENNReal) *
          (r : ENNReal) ^ 2 * (δ : ENNReal) ^ 2 := by
          ring
    _ = (Tube.le_volume.c 3 : ENNReal) * (r : ENNReal) ^ 2 * (δ : ENNReal) ^ 2 := by
          rw [hc_mul]
    _ = (δ : ENNReal) ^ 2 * ((Tube.le_volume.c 3 : ENNReal) * (r : ENNReal) ^ 2) := by
          ring
    _ ≤ (δ : ENNReal) ^ 2 * ((Tube.le_volume.c 3 : ENNReal) * (ρ : ENNReal) ^ 2) := by
          gcongr

/-- The volume of a ball scales as the cube of its radius in `ℝ³`, in the division-free form
that the ball estimate of blueprint `lowerBoundTTScaleAAndABall` needs when its radius is
moved from the grid scale `ρ` down to the nominal radius `r`. -/
theorem volume_ball_mul_pow_comm (x : EuclideanSpace ℝ (Fin 3)) (r ρ : NNReal) :
    (r : ENNReal) ^ 3 * volume (ball x (ρ : ℝ)) =
      (ρ : ENNReal) ^ 3 * volume (ball x (r : ℝ)) := by
  rw [EuclideanSpace.volume_ball, EuclideanSpace.volume_ball]
  simp
  ring

namespace VeryNotSticky

open StickyKakeya

variable {N : ℕ} {C₀ : NNReal}

/-! ### Elementary facts about the node family -/

/-- A node carrying a member of `𝕋` is a node: the active nodes sit inside the index set. -/
theorem mem_indexSet_of_mem_activeTubeNodes (cfg : VeryNotSticky)
    (𝒰 : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube) N C₀) {k : ℕ} {j : cfg.ι}
    (hj : j ∈ cfg.activeTubeNodes 𝒰 k) : j ∈ 𝒰.cover.indexSet k := by
  simpa [VeryNotSticky.activeTubeNodes] using (Finset.mem_filter.mp hj).1

/-- **The parent family at a grid level is nonempty** as soon as `𝕋` is.

Every member of `𝕋` is assigned to a node (`Tube.GridCoverSystem.assign_mem`), and
that node then carries a nonempty class, so it is active. This is what supplies the side
condition `Na ≠ 0` of `Kakeya.VeryNotSticky.aScaleVolume`, which the docstring of
`Kakeya.VeryNotSticky.coarseVolumeLower` records as not decorative: at `Na = ⊤` — and, for
`β = 1`, at `Na = 0` — that lemma is refutable. -/
theorem activeTubeNodes_nonempty (cfg : VeryNotSticky)
    (𝒰 : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube) N C₀) {k : ℕ} (hk : k ≤ N)
    (hs : cfg.s.Nonempty) : (cfg.activeTubeNodes 𝒰 k).Nonempty := by
  classical
  rcases hs with ⟨i, hi⟩
  refine ⟨𝒰.cover.assign k i, ?_⟩
  simp only [activeTubeNodes, Finset.mem_filter]
  refine ⟨𝒰.cover.assign_mem k hk i hi, ⟨i, ?_⟩⟩
  simp [tubeFibre, Tube.coverClass, hi]

/-- `𝕋` is nonempty, from the fixed-scale count (C1) `1 ≤ δ |𝕋|` of Configuration
`hyp:ml2setup`. -/
theorem s_nonempty (cfg : VeryNotSticky) : cfg.s.Nonempty := by
  by_contra hne
  have hcard0 : (cfg.s.card : ENNReal) = 0 := by
    have hsempty : cfg.s = ∅ := by
      rw [Finset.not_nonempty_iff_eq_empty] at hne
      exact hne
    simp [hsempty]
  have hbad : (1 : ENNReal) ≤ 0 := by
    calc
      (1 : ENNReal) ≤ (cfg.δ : ENNReal) * (cfg.s.card : ENNReal) := cfg.tube_count
      _ = 0 := by simp [hcard0]
  exact (by norm_num : ¬ (1 : ENNReal) ≤ 0) hbad

/-! ### The uniformity constant is sub-polynomial -/

/-- **The branching/overlap constant of the configuration satisfies `C₀ ≤ δ^{-η}`.**

Configuration `hyp:ml2setup` carries `aScaleData_absorb`, `C_⋆(C₀, D₀)² ≤ δ^{-η}` with
`C_⋆ = Kakeya.aScaleDataConstant C₀ D₀`, and `C_⋆ ≥ Kakeya.aScaleVolumeConstant C₀ D₀ ≥ C₀²`,
since `aScaleVolumeConstant C₀ D₀ = C₀² · C_{lem:ml2DeltamaxScaleA}(C₀, D₀) / c` with
`c = Kakeya.tubeVolumeRatioConstant 3 ≤ 1` and `C_{lem:ml2DeltamaxScaleA} ≥ 1`. So the clause
that absorbs the accumulated comparison constant absorbs `C₀` along with it.

This is what makes the losses proportional to `C₀` in the scale-`r` layer sub-polynomial, and
it is why the two statements of `Kakeya.DimensionThree.MainLemma2.AScaleResidues` may be stated
without a `C₀` in their conclusions: the substitution of the bounded overlap of blueprint
`uniformSetOfTubes`(ii) for pairwise essential distinctness costs a factor `C₀`, and this bound
is where that factor is charged. It is available only because the bundle is the configuration's
own; at a `C₀` quantified before the statement there is nothing to charge it to. -/
theorem coe_C₀_le_rpow_neg_eta (cfg : VeryNotSticky) :
    (cfg.C₀ : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-cfg.η) := by
  have hC₀le : cfg.C₀ ≤ cfg.C₀ ^ 2 := by
    calc
      cfg.C₀ = cfg.C₀ * 1 := by rw [mul_one]
      _ ≤ cfg.C₀ * cfg.C₀ := by
        exact mul_le_mul_of_nonneg_left cfg.hC₀ (by positivity)
      _ = cfg.C₀ ^ 2 := by rw [pow_two]
  have hC2le : cfg.C₀ ^ 2 ≤ cfg.C₀ ^ 2 * deltamaxScaleAConstant cfg.C₀ cfg.D₀ := by
    calc
      cfg.C₀ ^ 2 = cfg.C₀ ^ 2 * 1 := by rw [mul_one]
      _ ≤ cfg.C₀ ^ 2 * deltamaxScaleAConstant cfg.C₀ cfg.D₀ := by
        exact mul_le_mul_of_nonneg_left (one_le_deltamaxScaleAConstant cfg.hC₀ cfg.hD₀)
          (by positivity : 0 ≤ cfg.C₀ ^ 2)
  have hvol : cfg.C₀ ^ 2 * deltamaxScaleAConstant cfg.C₀ cfg.D₀ ≤
      aScaleVolumeConstant cfg.C₀ cfg.D₀ := by
    rw [aScaleVolumeConstant]
    rw [le_div_iff₀ (tubeVolumeRatioConstant_pos 3)]
    calc
      (cfg.C₀ ^ 2 * deltamaxScaleAConstant cfg.C₀ cfg.D₀) * tubeVolumeRatioConstant 3
          ≤ (cfg.C₀ ^ 2 * deltamaxScaleAConstant cfg.C₀ cfg.D₀) * 1 := by
            exact mul_le_mul_of_nonneg_left tubeVolumeRatioConstant_three_le_one
              (by positivity : 0 ≤ (cfg.C₀ ^ 2 * deltamaxScaleAConstant cfg.C₀ cfg.D₀))
      _ = cfg.C₀ ^ 2 * deltamaxScaleAConstant cfg.C₀ cfg.D₀ := by
        rw [mul_one]
  have hCst_le : aScaleDataConstant cfg.C₀ cfg.D₀ ≤
      aScaleDataConstant cfg.C₀ cfg.D₀ ^ 2 := by
    calc
      aScaleDataConstant cfg.C₀ cfg.D₀ = aScaleDataConstant cfg.C₀ cfg.D₀ * 1 := by
        rw [mul_one]
      _ ≤ aScaleDataConstant cfg.C₀ cfg.D₀ * aScaleDataConstant cfg.C₀ cfg.D₀ := by
        exact mul_le_mul_of_nonneg_left (one_le_aScaleDataConstant cfg.hC₀ cfg.hD₀)
          (by positivity : 0 ≤ aScaleDataConstant cfg.C₀ cfg.D₀)
      _ = aScaleDataConstant cfg.C₀ cfg.D₀ ^ 2 := by
        rw [pow_two]
  have hNN : cfg.C₀ ≤ aScaleDataConstant cfg.C₀ cfg.D₀ ^ 2 := by
    calc
      cfg.C₀ ≤ cfg.C₀ ^ 2 := hC₀le
      _ ≤ aScaleVolumeConstant cfg.C₀ cfg.D₀ := by
        calc
          cfg.C₀ ^ 2 ≤ cfg.C₀ ^ 2 * deltamaxScaleAConstant cfg.C₀ cfg.D₀ := hC2le
          _ ≤ aScaleVolumeConstant cfg.C₀ cfg.D₀ := hvol
      _ ≤ aScaleDataConstant cfg.C₀ cfg.D₀ :=
        aScaleVolumeConstant_le_aScaleDataConstant cfg.C₀ cfg.D₀
      _ ≤ aScaleDataConstant cfg.C₀ cfg.D₀ ^ 2 := hCst_le
  calc
    (cfg.C₀ : ENNReal) ≤ (aScaleDataConstant cfg.C₀ cfg.D₀ : ENNReal) ^ 2 := by
      exact_mod_cast hNN
    _ ≤ (cfg.δ : ENNReal) ^ (-cfg.η) := cfg.aScaleData_absorb

/-! ### The reference tube volume -/

/-- The mean volume of a tube of `𝕋`.

Blueprint `volumeOfTTa` writes `∑_{T ∈ 𝕋} |T| = |T| |𝕋|` with `|T|` "the" tube volume; the
Lean development has no congruence lemma for tubes, so there is no common value to name. The
mean does the same work: it factors the sum exactly (`Kakeya.VeryNotSticky.sum_volume_eq`) and
it inherits the dimensional upper bound of `Tube.volume_le`
(`Kakeya.VeryNotSticky.meanTubeVolume_le`), which is all that the tube-volume comparison
needs. -/
noncomputable def meanTubeVolume (cfg : VeryNotSticky) : ENNReal :=
  (∑ i ∈ cfg.s, volume (cfg.T i).toShadedBody.carrier) / (cfg.s.card : ENNReal)

/-- The mean tube volume factors `∑_{T ∈ 𝕋} |T|` exactly, which is the hypothesis `hS` of
`Kakeya.VeryNotSticky.aScaleVolume`. -/
theorem sum_volume_eq (cfg : VeryNotSticky) :
    ∑ i ∈ cfg.s, volume (cfg.T i).toShadedBody.carrier =
      cfg.meanTubeVolume * (cfg.s.card : ENNReal) := by
  unfold meanTubeVolume
  symm
  rw [mul_comm]
  exact ENNReal.mul_div_cancel
    (by
      have hpos : 0 < cfg.s.card := Finset.card_pos.mpr (s_nonempty cfg)
      exact_mod_cast (ne_of_gt hpos))
    (ENNReal.natCast_ne_top cfg.s.card)

/-- The mean tube volume obeys the dimensional upper bound of `Tube.volume_le`, since
every summand does. -/
theorem meanTubeVolume_le (cfg : VeryNotSticky) :
    cfg.meanTubeVolume ≤ (Tube.volume_le.C 3 : ENNReal) * (cfg.δ : ENNReal) ^ 2 := by
  let C : ENNReal := (Tube.volume_le.C 3 : ENNReal) * (cfg.δ : ENNReal) ^ 2
  have hvol : ∀ i, i ∈ cfg.s → volume (cfg.T i).toShadedBody.carrier ≤ C := by
    intro i hi
    have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := finrank_euclideanSpace_fin
    simpa [C, hfin] using (Tube.volume_le cfg.hδ1 (cfg.T i).toTube)
  have hS : (∑ i ∈ cfg.s, volume (cfg.T i).toShadedBody.carrier) ≤ (cfg.s.card : ENNReal) * C := by
    calc
      (∑ i ∈ cfg.s, volume (cfg.T i).toShadedBody.carrier) ≤ ∑ i ∈ cfg.s, C :=
        Finset.sum_le_sum (fun i hi => hvol i hi)
      _ = (cfg.s.card : ENNReal) * C := by
        rw [Finset.sum_const, nsmul_eq_mul]
  by_cases hn : (cfg.s.card : ENNReal) = 0
  · have hcard : cfg.s.card = 0 := by exact_mod_cast hn
    have hs : cfg.s = ∅ := Finset.card_eq_zero.mp hcard
    have hS0 : (∑ i ∈ cfg.s, volume (cfg.T i).toShadedBody.carrier) = 0 := by simp [hs]
    unfold meanTubeVolume
    rw [hS0, hn]
    simp
  · exact (ENNReal.div_le_iff_le_mul (Or.inl hn) (Or.inl (ENNReal.natCast_ne_top cfg.s.card))).2
      (by simpa [C, mul_comm] using hS)

/-! ### Rounding the radius to the grid -/

/-- The grid of GWZ Definition 2.1 has positive length, from
`Kakeya.VeryNotSticky.gridFine` and `cfg.hη`. -/
theorem ssfGridLen_pos (cfg : VeryNotSticky) : 0 < Tube.ssfGridLen cfg.δ := by
  apply Nat.pos_of_ne_zero
  intro hz
  have hle : (1 : ℝ) ≤ cfg.η * (Tube.ssfGridLen cfg.δ : ℝ) := cfg.gridFine
  have hz0 : cfg.η * (Tube.ssfGridLen cfg.δ : ℝ) = 0 := by
    rw [hz]
    simp
  have : (1 : ℝ) ≤ (0 : ℝ) := by simpa [hz0] using hle
  exact (not_le_of_gt zero_lt_one) this

/-- **One grid step costs at most `δ^{-η}`** — the content of the configuration's field
`Kakeya.VeryNotSticky.gridFine`, in the form the estimates use.

Consecutive scales of the grid of GWZ Definition 2.1 differ by `δ^{1/⌈log log 1/δ⌉}`, and
`gridFine` says `1 ≤ η ⌈log log 1/δ⌉`, so the step is at most `δ^{-η}`
(`Kakeya.StickyKakeya.rpow_neg_div_le_rpow_neg`). -/
theorem gridStep_le (cfg : VeryNotSticky) :
    (cfg.δ : NNReal) ^ (-(1 : ℝ) / (Tube.ssfGridLen cfg.δ : ℝ)) ≤
      cfg.δ ^ (-cfg.η) := by
  exact StickyKakeya.rpow_neg_div_le_rpow_neg cfg.hδ cfg.hδ1
    (ssfGridLen_pos cfg) cfg.gridFine

/-- **Rounding the radius of the scale-`r` layer up to the multiscale grid.**

For `cfg.a ≤ r ≤ 1` there is a grid index `k ≤ ⌈log log 1/δ⌉` whose scale `ρ` satisfies
`r ≤ ρ ≤ δ^{-η} r`, and `ρ ≤ 1`. Both halves are `Kakeya.StickyKakeya.exists_gridScale_ge`,
whose range hypothesis `r ∈ [δ, 1]` holds because `cfg.hdims` gives `δ ≤ a ≤ r`; the
conversion of the grid step `δ^{-1/N}` into `δ^{-η}` is
`Kakeya.VeryNotSticky.gridStep_le`.

This is the whole of what the third remark of blueprint `lem:ml2aScaleData` called a genuine
obstruction. It is not one: the grid length of GWZ Definition 2.1 is `log log 1/δ` precisely so
that one grid step is sub-polynomial, and GWZ perform the same rounding by hand at p. 41 at the
strictly greater cost `δ^{3η}`. -/
theorem exists_gridIndex (cfg : VeryNotSticky) {r : NNReal} (hr : cfg.a ≤ r) (hr1 : r ≤ 1) :
    ∃ k ≤ Tube.ssfGridLen cfg.δ,
      r ≤ Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k ∧
        Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k ≤
          cfg.δ ^ (-cfg.η) * r := by
  have hδr : cfg.δ ≤ r := le_trans cfg.hdims.1 hr
  rcases StickyKakeya.exists_gridScale_ge (δ := cfg.δ) cfg.hδ cfg.hδ1
      (N := Tube.ssfGridLen cfg.δ) (hN := ssfGridLen_pos cfg) (r := r) ⟨hδr, hr1⟩ with
    ⟨k, hk, hle1, hle2⟩
  refine ⟨k, hk, hle1, ?_⟩
  calc
    Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k ≤
        cfg.δ ^ (-(1 : ℝ) / (Tube.ssfGridLen cfg.δ : ℝ)) * r := hle2
    _ ≤ cfg.δ ^ (-cfg.η) * r := by
      exact mul_le_mul_of_nonneg_right (gridStep_le cfg) (by positivity)

/-! ### Charging the two losses to the gain -/

/-- **The multiplicity loss fits in `δ^{ν/45}`.**

If `ρ ≤ δ^{-η} r` then `δ^{ν/45} ρ² ≤ r²`, because `ν ≥ 90 η` gives `2η ≤ ν/45` and
`0 < δ ≤ 1` makes `s ↦ δ^s` antitone. This is what lets the parent multiplicity be taken to be
`δ^{ν/45}` times the honest `δ^η Δ_max(𝕋_ρ)`, which is how the two-scale multiplicity bound of
blueprint `lem:ml2DeltamaxScaleA` is transported from the grid scale `ρ` down to the nominal
radius `r` with the constant `Kakeya.deltamaxScaleAConstant` unchanged. -/
theorem rpow_mul_sq_le_sq_of_gridStep (cfg : VeryNotSticky) {ν : ℝ} (hνη : 90 * cfg.η ≤ ν)
    {r ρ : NNReal} (hρ : ρ ≤ cfg.δ ^ (-cfg.η) * r) :
    (cfg.δ : ENNReal) ^ (ν / 45) * (ρ : ENNReal) ^ 2 ≤ (r : ENNReal) ^ 2 := by
  have hδ0 : cfg.δ ≠ 0 := cfg.hδ.ne'
  have hρ2 : ρ ^ 2 ≤ (cfg.δ ^ (-cfg.η) * r) ^ 2 := by
    exact pow_le_pow_left₀ (by positivity : 0 ≤ ρ) hρ 2
  have hrpow : ρ ^ 2 ≤ cfg.δ ^ (-(2 * cfg.η)) * r ^ 2 := by
    calc
      ρ ^ 2 ≤ (cfg.δ ^ (-cfg.η) * r) ^ 2 := hρ2
      _ = (cfg.δ ^ (-cfg.η)) ^ 2 * r ^ 2 := by rw [mul_pow]
      _ = cfg.δ ^ (-(2 * cfg.η)) * r ^ 2 := by
        congr 1
        rw [← NNReal.rpow_mul_natCast cfg.δ (-cfg.η) 2]
        congr 1
        ring
  have h2η : 2 * cfg.η ≤ ν / 45 := by nlinarith
  have hz : 0 ≤ ν / 45 - 2 * cfg.η := by linarith
  have hcomb : cfg.δ ^ (ν / 45) * (cfg.δ ^ (-(2 * cfg.η)) * r ^ 2) =
      cfg.δ ^ (ν / 45 - 2 * cfg.η) * r ^ 2 := by
    calc
      cfg.δ ^ (ν / 45) * (cfg.δ ^ (-(2 * cfg.η)) * r ^ 2)
          = (cfg.δ ^ (ν / 45) * cfg.δ ^ (-(2 * cfg.η))) * r ^ 2 := by rw [mul_assoc]
      _ = cfg.δ ^ (ν / 45 + (-(2 * cfg.η))) * r ^ 2 := by
        rw [NNReal.rpow_add hδ0 (ν / 45) (-(2 * cfg.η))]
      _ = cfg.δ ^ (ν / 45 - 2 * cfg.η) * r ^ 2 := by
        rw [show ν / 45 + (-(2 * cfg.η)) = ν / 45 - 2 * cfg.η by ring]
  have hmain : cfg.δ ^ (ν / 45) * ρ ^ 2 ≤ cfg.δ ^ (ν / 45 - 2 * cfg.η) * r ^ 2 := by
    calc
      cfg.δ ^ (ν / 45) * ρ ^ 2
          ≤ cfg.δ ^ (ν / 45) * (cfg.δ ^ (-(2 * cfg.η)) * r ^ 2) := by
            exact mul_le_mul_of_nonneg_left hrpow (by positivity)
      _ = cfg.δ ^ (ν / 45 - 2 * cfg.η) * r ^ 2 := hcomb
  have hle1 : cfg.δ ^ (ν / 45 - 2 * cfg.η) ≤ 1 :=
    NNReal.rpow_le_one cfg.hδ1 hz
  have hfin : cfg.δ ^ (ν / 45 - 2 * cfg.η) * r ^ 2 ≤ r ^ 2 := by
    calc
      cfg.δ ^ (ν / 45 - 2 * cfg.η) * r ^ 2 ≤ 1 * r ^ 2 := by
        exact mul_le_mul_of_nonneg_right hle1 (by positivity)
      _ = r ^ 2 := by simp
  exact_mod_cast (le_trans hmain hfin)


/-- **The multiplicity loss fits in `δ^{2η}`.**

The tight form of `Kakeya.VeryNotSticky.rpow_mul_sq_le_sq_of_gridStep`: one grid step costs
`(ρ/r)² ≤ δ^{-2η}`, and `δ^{2η}` is exactly what pays for it — no hypothesis relating `ν` to
`η` is needed, because no surplus is created. The `ν/45` of that lemma is inherited generosity
from the `ν/9` budget of blueprint `lem:ml2aScaleExponentBudget`; its own proof passes through
`2η ≤ ν/45` and then discards the surplus `δ^{ν/45 - 2η} ≤ 1`.

This is the version `Kakeya.VeryNotSticky.rScaleParentData_of_gridScale` uses, so that the
parent multiplicity it produces is `δ^{2η} δ^{η} Δ_max(𝕋_ρ)` rather than
`δ^{ν/45} δ^{η} Δ_max(𝕋_ρ)`. The difference is not cosmetic: the larger factor `δ^{ν/45}` is a
*strengthening* of the Katz–Tao input that has to be paid for out of the gain `a^{-ν/90}`, at
the exchange rate `cfg.exscal` of `cfg.hdims`, and the resulting budget
`(ν/45 + η)(1-β) < exscal · ν/90` is not satisfiable together with
`Kakeya.VeryNotSticky.CaseParams` below `β = 40/41`. -/
theorem rpow_two_eta_mul_sq_le_sq_of_gridStep (cfg : VeryNotSticky) {r ρ : NNReal}
    (hρ : ρ ≤ cfg.δ ^ (-cfg.η) * r) :
    (cfg.δ : ENNReal) ^ (2 * cfg.η) * (ρ : ENNReal) ^ 2 ≤ (r : ENNReal) ^ 2 := by
  have hδ0 : cfg.δ ≠ 0 := cfg.hδ.ne'
  have hrpow : ρ ^ 2 ≤ cfg.δ ^ (-(2 * cfg.η)) * r ^ 2 := by
    calc
      ρ ^ 2 ≤ (cfg.δ ^ (-cfg.η) * r) ^ 2 := pow_le_pow_left₀ (by positivity : 0 ≤ ρ) hρ 2
      _ = (cfg.δ ^ (-cfg.η)) ^ 2 * r ^ 2 := by rw [mul_pow]
      _ = cfg.δ ^ (-(2 * cfg.η)) * r ^ 2 := by
        congr 1
        rw [← NNReal.rpow_mul_natCast cfg.δ (-cfg.η) 2]
        congr 1
        ring
  have hmain : cfg.δ ^ (2 * cfg.η) * ρ ^ 2 ≤ r ^ 2 := by
    calc
      cfg.δ ^ (2 * cfg.η) * ρ ^ 2
          ≤ cfg.δ ^ (2 * cfg.η) * (cfg.δ ^ (-(2 * cfg.η)) * r ^ 2) :=
            mul_le_mul_of_nonneg_left hrpow (by positivity)
      _ = (cfg.δ ^ (2 * cfg.η) * cfg.δ ^ (-(2 * cfg.η))) * r ^ 2 := by rw [mul_assoc]
      _ = r ^ 2 := by
        rw [← NNReal.rpow_add hδ0]
        simp
  exact_mod_cast hmain

/-- **The ball-estimate loss fits in `δ^{ν/9}`.**

If `ρ ≤ δ^{-η} r` then `δ^{ν/9} ρ³ ≤ r³`, because `ν ≥ 90 η` gives `3η ≤ ν/9`. This is the
payment for moving the estimate of blueprint `boundVolumeAcrossTwoScales` from balls of the
grid radius `ρ` to balls of the nominal radius `r`, the ratio of ball volumes in `ℝ³` being
`(ρ/r)³`. GWZ make the same payment at p. 41, at the cost `δ^{3η}`. -/
theorem rpow_mul_cube_le_cube_of_gridStep (cfg : VeryNotSticky) {ν : ℝ}
    (hνη : 90 * cfg.η ≤ ν) {r ρ : NNReal} (hρ : ρ ≤ cfg.δ ^ (-cfg.η) * r) :
    (cfg.δ : ENNReal) ^ (ν / 9) * (ρ : ENNReal) ^ 3 ≤ (r : ENNReal) ^ 3 := by
  have hδ0 : cfg.δ ≠ 0 := cfg.hδ.ne'
  have hρ3 : ρ ^ 3 ≤ (cfg.δ ^ (-cfg.η) * r) ^ 3 := by
    exact pow_le_pow_left₀ (by positivity : 0 ≤ ρ) hρ 3
  have hrpow : ρ ^ 3 ≤ cfg.δ ^ (-(3 * cfg.η)) * r ^ 3 := by
    calc
      ρ ^ 3 ≤ (cfg.δ ^ (-cfg.η) * r) ^ 3 := hρ3
      _ = (cfg.δ ^ (-cfg.η)) ^ 3 * r ^ 3 := by rw [mul_pow]
      _ = cfg.δ ^ (-(3 * cfg.η)) * r ^ 3 := by
        congr 1
        rw [← NNReal.rpow_mul_natCast cfg.δ (-cfg.η) 3]
        congr 1
        ring
  have h3η : 3 * cfg.η ≤ ν / 9 := by nlinarith [hνη, cfg.hη]
  have hz : 0 ≤ ν / 9 - 3 * cfg.η := by linarith
  have hcomb : cfg.δ ^ (ν / 9) * (cfg.δ ^ (-(3 * cfg.η)) * r ^ 3) =
      cfg.δ ^ (ν / 9 - 3 * cfg.η) * r ^ 3 := by
    calc
      cfg.δ ^ (ν / 9) * (cfg.δ ^ (-(3 * cfg.η)) * r ^ 3)
          = (cfg.δ ^ (ν / 9) * cfg.δ ^ (-(3 * cfg.η))) * r ^ 3 := by rw [mul_assoc]
      _ = cfg.δ ^ (ν / 9 + (-(3 * cfg.η))) * r ^ 3 := by
        rw [NNReal.rpow_add hδ0 (ν / 9) (-(3 * cfg.η))]
      _ = cfg.δ ^ (ν / 9 - 3 * cfg.η) * r ^ 3 := by
        rw [show ν / 9 + (-(3 * cfg.η)) = ν / 9 - 3 * cfg.η by ring]
  have hmain : cfg.δ ^ (ν / 9) * ρ ^ 3 ≤ cfg.δ ^ (ν / 9 - 3 * cfg.η) * r ^ 3 := by
    calc
      cfg.δ ^ (ν / 9) * ρ ^ 3
          ≤ cfg.δ ^ (ν / 9) * (cfg.δ ^ (-(3 * cfg.η)) * r ^ 3) := by
            exact mul_le_mul_of_nonneg_left hrpow (by positivity)
      _ = cfg.δ ^ (ν / 9 - 3 * cfg.η) * r ^ 3 := hcomb
  have hle1 : cfg.δ ^ (ν / 9 - 3 * cfg.η) ≤ 1 :=
    NNReal.rpow_le_one cfg.hδ1 hz
  have hfin : cfg.δ ^ (ν / 9 - 3 * cfg.η) * r ^ 3 ≤ r ^ 3 := by
    calc
      cfg.δ ^ (ν / 9 - 3 * cfg.η) * r ^ 3 ≤ 1 * r ^ 3 := by
        exact mul_le_mul_of_nonneg_right hle1 (by positivity)
      _ = r ^ 3 := by simp
  exact_mod_cast (le_trans hmain hfin)

/-- **The ball-estimate loss still fits after one factor `δ^η` has been spent.**

If `ρ ≤ δ^{-η} r` then `δ^{ν/9 - η} ρ³ ≤ r³`, because `ν ≥ 90 η` and `η > 0` give
`ν/9 - η ≥ 10η - η = 9η ≥ 3η`. Equivalently, the inequality needs `ν ≥ 36 η` and the standing
budget supplies `ν ≥ 90 η`, so the surplus is `ν/9 - 4η ≥ 6η`.

This is the form of `Kakeya.VeryNotSticky.rpow_mul_cube_le_cube_of_gridStep` used once the ball
conjunct of `Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid` carries a factor `δ^{cfg.η}`
on its small side — the room out of which the substitution of bounded overlap for pairwise
essential distinctness pays its factor `C₀`, sub-polynomial by
`Kakeya.VeryNotSticky.coe_C₀_le_rpow_neg_eta`. The two payments are made against the same
budget and are made only once each: `η` for the overlap substitution and `3η` for the change
of ball radius. -/
theorem rpow_sub_eta_mul_cube_le_cube_of_gridStep (cfg : VeryNotSticky) {ν : ℝ}
    (hνη : 90 * cfg.η ≤ ν) {r ρ : NNReal} (hρ : ρ ≤ cfg.δ ^ (-cfg.η) * r) :
    (cfg.δ : ENNReal) ^ (ν / 9 - cfg.η) * (ρ : ENNReal) ^ 3 ≤ (r : ENNReal) ^ 3 := by
  have hδ0 : cfg.δ ≠ 0 := cfg.hδ.ne'
  have hρ3 : ρ ^ 3 ≤ (cfg.δ ^ (-cfg.η) * r) ^ 3 := by
    exact pow_le_pow_left₀ (by positivity : 0 ≤ ρ) hρ 3
  have hrpow : ρ ^ 3 ≤ cfg.δ ^ (-(3 * cfg.η)) * r ^ 3 := by
    calc
      ρ ^ 3 ≤ (cfg.δ ^ (-cfg.η) * r) ^ 3 := hρ3
      _ = (cfg.δ ^ (-cfg.η)) ^ 3 * r ^ 3 := by rw [mul_pow]
      _ = cfg.δ ^ (-(3 * cfg.η)) * r ^ 3 := by
        congr 1
        rw [← NNReal.rpow_mul_natCast cfg.δ (-cfg.η) 3]
        congr 1
        ring
  have h3η : 3 * cfg.η ≤ ν / 9 - cfg.η := by nlinarith [hνη, cfg.hη]
  have hz : 0 ≤ ν / 9 - cfg.η - 3 * cfg.η := by linarith
  have hcomb : cfg.δ ^ (ν / 9 - cfg.η) * (cfg.δ ^ (-(3 * cfg.η)) * r ^ 3) =
      cfg.δ ^ (ν / 9 - cfg.η - 3 * cfg.η) * r ^ 3 := by
    calc
      cfg.δ ^ (ν / 9 - cfg.η) * (cfg.δ ^ (-(3 * cfg.η)) * r ^ 3)
          = (cfg.δ ^ (ν / 9 - cfg.η) * cfg.δ ^ (-(3 * cfg.η))) * r ^ 3 := by rw [mul_assoc]
      _ = cfg.δ ^ (ν / 9 - cfg.η + (-(3 * cfg.η))) * r ^ 3 := by
        rw [NNReal.rpow_add hδ0 (ν / 9 - cfg.η) (-(3 * cfg.η))]
      _ = cfg.δ ^ (ν / 9 - cfg.η - 3 * cfg.η) * r ^ 3 := by
        rw [show ν / 9 - cfg.η + (-(3 * cfg.η)) = ν / 9 - cfg.η - 3 * cfg.η by ring]
  have hmain : cfg.δ ^ (ν / 9 - cfg.η) * ρ ^ 3 ≤ cfg.δ ^ (ν / 9 - cfg.η - 3 * cfg.η) * r ^ 3 := by
    calc
      cfg.δ ^ (ν / 9 - cfg.η) * ρ ^ 3
          ≤ cfg.δ ^ (ν / 9 - cfg.η) * (cfg.δ ^ (-(3 * cfg.η)) * r ^ 3) := by
            exact mul_le_mul_of_nonneg_left hrpow (by positivity)
      _ = cfg.δ ^ (ν / 9 - cfg.η - 3 * cfg.η) * r ^ 3 := hcomb
  have hle1 : cfg.δ ^ (ν / 9 - cfg.η - 3 * cfg.η) ≤ 1 :=
    NNReal.rpow_le_one cfg.hδ1 hz
  have hfin : cfg.δ ^ (ν / 9 - cfg.η - 3 * cfg.η) * r ^ 3 ≤ r ^ 3 := by
    calc
      cfg.δ ^ (ν / 9 - cfg.η - 3 * cfg.η) * r ^ 3 ≤ 1 * r ^ 3 := by
        exact mul_le_mul_of_nonneg_right hle1 (by positivity)
      _ = r ^ 3 := by simp
  exact_mod_cast (le_trans hmain hfin)

end VeryNotSticky

end Kakeya

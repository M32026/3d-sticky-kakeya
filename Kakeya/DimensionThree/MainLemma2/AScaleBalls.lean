/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Covers
public import Kakeya.FactorFamily.Basic

/-!
# Ball geometry for the scale-`a` estimates of Main Lemma 2

The four elementary ball statements of the scale-`a` layer of Section 9
(`blueprint/src/GWZAdapted/section9_setup.tex`), together with the one shading statement that
goes with them:

* blueprint `lem:ml2packingBound`, the packing bound `#F ≤ 5 ^ n` for an `r/2`-separated
  subset of an `r`-ball;
* blueprint `lem:ballCoverHalfRadius`, the cover of an `r`-ball by at most `5 ^ n` closed
  balls of radius `r/2`;
* blueprint `lem:ml2ballPigeonhole`, a half-radius piece of the cover carrying a `5^{-n}`
  fraction of the mass;
* blueprint `lem:ml2ballRecentre`, re-centring the ball at a point of the set itself, which is
  the form blueprint `boundVolumeAcrossTwoScales` needs;
* blueprint `lem:ml2coarseShaded`, that a point shaded at the fine scale is shaded at the
  coarse one.

All four reduce to the separated-net API of `Kakeya/Covers.lean`, and the fifth is the
`shade_subset_parent` field of `ShadedBody.ShadedFactorFamily` read at the level of unions.
They are consumed in `Kakeya/DimensionThree/MainLemma2/AScaleSetup.lean`, which carries the
rest of that layer.
-/

@[expose] public section

namespace Kakeya

open MeasureTheory Metric Set

section Balls

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Packing bound for a ball** (blueprint `lem:ml2packingBound`).

An `r/2`-separated subset of a ball of radius `r` is finite of cardinality at most
`5 ^ n = Kakeya.separatedNetCoverConstant n`. In the ambient dimension `n = 3` of Section 9
this is the `5 ^ 3` of the blueprint.

This is `Kakeya.finite_and_card_le_of_separated` at separation `r / 2` inside a ball of
radius `R = r`, where the general bound `(1 + 2R/r')^n` evaluates to `5 ^ n`. -/
theorem packing_ball_half {r : ℝ} (hr : 0 < r) (x₀ : E) {F : Set E}
    (hsep : ∀ y ∈ F, ∀ z ∈ F, y ≠ z → r / 2 ≤ dist y z) (hF : F ⊆ ball x₀ r) :
    F.Finite ∧ (F.ncard : ℝ) ≤ (separatedNetCoverConstant (Module.finrank ℝ E) : ℝ) := by
  classical
  have h := Kakeya.finite_and_card_le_of_separated (r := r / 2) (R := r) (hr := by positivity)
      (hR := le_of_lt hr) (x₀ := x₀) (N := F) hsep hF
  refine ⟨h.1, ?_⟩
  have hcalc : (1 + 2 * r / (r / 2)) = (5 : ℝ) := by
    field_simp [ne_of_gt hr]
    ring
  calc
    (F.ncard : ℝ) ≤ (1 + 2 * r / (r / 2)) ^ Module.finrank ℝ E := h.2
    _ = (separatedNetCoverConstant (Module.finrank ℝ E) : ℝ) := by
      rw [Kakeya.separatedNetCoverConstant, hcalc]
      norm_num

/-- **Covering a ball by balls of half the radius** (blueprint `lem:ballCoverHalfRadius`).

A ball of radius `r` is covered by at most `5 ^ n` closed balls of radius `r / 2` centred in
it. The centres are a maximal `r/2`-separated subset, whose cardinality is bounded by
`Kakeya.packing_ball_half`; maximality is what gives the covering property.

The covering balls are closed. Every measure estimate made from this cover is insensitive to
the distinction, the sphere being null. -/
theorem exists_finset_cover_closedBall_half {r : ℝ} (hr : 0 < r) (x₀ : E) :
    ∃ F : Finset E, ↑F ⊆ ball x₀ r ∧
      (F.card : ℝ) ≤ (separatedNetCoverConstant (Module.finrank ℝ E) : ℝ) ∧
      ball x₀ r ⊆ ⋃ z ∈ F, closedBall z (r / 2) := by
  classical
  have hBdd : Bornology.IsBounded (ball x₀ r) := Metric.isBounded_ball
  have hr2 : 0 < r / 2 := by positivity
  rcases exists_separatedNetCover hBdd hr2 with ⟨N, hNsub, _hsep, hmax, _hcov, _hcov₂, _hdisj,
    hcard⟩
  refine ⟨N, hNsub, ?_, ?_⟩
  · have hcard_le : (N.card : ℝ) ≤ (1 + 2 * r / (r / 2)) ^ Module.finrank ℝ E :=
      hcard x₀ r (le_of_lt hr) subset_rfl
    calc
      (N.card : ℝ) ≤ (1 + 2 * r / (r / 2)) ^ Module.finrank ℝ E := hcard_le
      _ = (5 : ℝ) ^ Module.finrank ℝ E := by
        have hcalc : (1 + 2 * r / (r / 2) : ℝ) = 5 := by
          field_simp [hr.ne']
          ring
        rw [hcalc]
      _ = (separatedNetCoverConstant (Module.finrank ℝ E) : ℝ) := by
        rw [separatedNetCoverConstant]
        norm_num
  · intro x hx
    rcases hmax x hx with ⟨y, hyN, hxy⟩
    refine Set.mem_iUnion₂.mpr ⟨y, hyN, ?_⟩
    exact Metric.mem_closedBall.mpr (le_of_lt hxy)

/-- **A half-radius piece carrying a fixed fraction** (blueprint `lem:ml2ballPigeonhole`).

If a set `S` meets a ball of radius `r` in positive measure then one of the at most `5 ^ n`
closed half-radius balls of the cover of `Kakeya.exists_finset_cover_closedBall_half` carries
at least a `5^{-n}` fraction of that measure.

Subadditivity over the finite cover gives
`|S ∩ B_r| ≤ ∑_{z ∈ F} |S ∩ B̄(z, r/2)|`, and `F` is nonempty with `#F ≤ 5 ^ n`. -/
theorem exists_volume_inter_closedBall_half_ge {S : Set E} {x₀ : E} {r : ℝ} (hr : 0 < r)
    (hpos : 0 < volume (S ∩ ball x₀ r)) :
    ∃ z ∈ ball x₀ r,
      volume (S ∩ ball x₀ r) ≤
          (separatedNetCoverConstant (Module.finrank ℝ E) : ENNReal) *
            volume (S ∩ closedBall z (r / 2)) ∧
        0 < volume (S ∩ closedBall z (r / 2)) := by
  rcases exists_finset_cover_closedBall_half hr x₀ with ⟨F, hFsub, hFcard, hFcover⟩
  let C : ENNReal := separatedNetCoverConstant (Module.finrank ℝ E)
  have hFne : F.Nonempty := by
    have hSne : (S ∩ ball x₀ r).Nonempty := nonempty_of_measure_ne_zero (ne_of_gt hpos)
    rcases hSne with ⟨x, hx⟩
    rcases Set.mem_iUnion₂.mp (hFcover hx.2) with ⟨z, hzF, _⟩
    exact ⟨z, hzF⟩
  have hcoverS : S ∩ ball x₀ r ⊆ ⋃ z ∈ F, S ∩ closedBall z (r / 2) := by
    intro x hx
    rcases Set.mem_iUnion₂.mp (hFcover hx.2) with ⟨z, hzF, hzclosed⟩
    exact Set.mem_biUnion hzF ⟨hx.1, hzclosed⟩
  have hvol : volume (S ∩ ball x₀ r) ≤ ∑ z ∈ F, volume (S ∩ closedBall z (r / 2)) := by
    calc
      volume (S ∩ ball x₀ r) ≤ volume (⋃ z ∈ F, S ∩ closedBall z (r / 2)) :=
        measure_mono hcoverS
      _ ≤ ∑ z ∈ F, volume (S ∩ closedBall z (r / 2)) :=
        measure_biUnion_finset_le F (fun z => S ∩ closedBall z (r / 2))
  have hFcard_e : (F.card : ENNReal) ≤ C := by
    change (F.card : ENNReal) ≤ (separatedNetCoverConstant (Module.finrank ℝ E) : ENNReal)
    exact_mod_cast hFcard
  have hsum_le :
      ∑ z ∈ F, volume (S ∩ ball x₀ r) ≤
        ∑ z ∈ F, C * volume (S ∩ closedBall z (r / 2)) := by
    calc
      ∑ z ∈ F, volume (S ∩ ball x₀ r) = F.card * volume (S ∩ ball x₀ r) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ C * volume (S ∩ ball x₀ r) := by
        exact mul_le_mul' hFcard_e le_rfl
      _ ≤ C * ∑ z ∈ F, volume (S ∩ closedBall z (r / 2)) := by
        exact mul_le_mul' le_rfl hvol
      _ = ∑ z ∈ F, C * volume (S ∩ closedBall z (r / 2)) := by
        rw [Finset.mul_sum]
  rcases ENNReal.exists_le_of_sum_le hFne hsum_le with ⟨z, hzF, hz⟩
  have hzpos : 0 < volume (S ∩ closedBall z (r / 2)) := by
    have hCbpos : 0 < C * volume (S ∩ closedBall z (r / 2)) := lt_of_lt_of_le hpos hz
    exact (ENNReal.mul_pos_iff.mp hCbpos).2
  refine ⟨z, ?_, ?_, ?_⟩
  · simpa using hFsub hzF
  · simpa [C] using hz
  · exact hzpos

/-- **Re-centring a ball at a point of the set** (blueprint `lem:ml2ballRecentre`).

If `S` meets the ball `B(x₀, r)` then there is a point `x ∈ S` — not merely in the ball —
with `|S ∩ B(x₀, r)| ≤ 5 ^ n |S ∩ B(x, r)|`, at the same radius and hence at a ball of the
same measure.

The re-centred ball is *open*, which is what blueprint `boundVolumeAcrossTwoScales`, and so
`Kakeya.aScaleBall`, feeds on. No measurability of `S` is needed: this is
`Kakeya.exists_mem_volume_inter_ball_ge` applied to `S ∩ B(x₀, r)` at `K = 1`, whose constant
`(1 + 2)^n = 3 ^ n` is even better than the `5 ^ n` the blueprint records. -/
theorem exists_mem_volume_inter_ball_recentre {S : Set E} {x₀ : E} {r : ℝ} (hr : 0 < r)
    (hne : (S ∩ ball x₀ r).Nonempty) :
    ∃ x ∈ S,
      volume (S ∩ ball x₀ r) ≤
          (separatedNetCoverConstant (Module.finrank ℝ E) : ENNReal) * volume (S ∩ ball x r) ∧
        volume (ball x r) = volume (ball x₀ r) := by
  classical
  let S' : Set E := S ∩ ball x₀ r
  rcases exists_mem_volume_inter_ball_ge (S := S') hne hr (K := (1 : NNReal)) (by norm_num) x₀
      (by intro x hx; exact inter_subset_right hx) (by simp) with ⟨y, hyS', hmain⟩
  refine ⟨y, hyS'.1, ?_, ?_⟩
  · have hc : (massSubballConstant (Module.finrank ℝ E) 1 : ENNReal) =
        (((3 : NNReal) ^ Module.finrank ℝ E : NNReal) : ENNReal)⁻¹ := by
      norm_num [massSubballConstant]
    have h3n0 : (((3 : NNReal) ^ Module.finrank ℝ E : NNReal) : ENNReal) ≠ 0 := by
      exact ENNReal.coe_ne_zero.mpr (pow_ne_zero _ (by norm_num))
    have h3ntop : (((3 : NNReal) ^ Module.finrank ℝ E : NNReal) : ENNReal) ≠ ⊤ := by
      exact ENNReal.coe_ne_top
    have hV : volume S' ≤ (((3 : NNReal) ^ Module.finrank ℝ E : NNReal) : ENNReal) *
        volume (S' ∩ ball y r) := by
      rw [hc] at hmain
      exact (ENNReal.inv_mul_le_iff h3n0 h3ntop).mp hmain
    have hsub : S' ∩ ball y r ⊆ S ∩ ball y r := by
      intro x hx
      exact ⟨hx.1.1, hx.2⟩
    have hmono : volume (S' ∩ ball y r) ≤ volume (S ∩ ball y r) := measure_mono hsub
    have h3le5 : (((3 : NNReal) ^ Module.finrank ℝ E : NNReal) : ENNReal) ≤
        (separatedNetCoverConstant (Module.finrank ℝ E) : ENNReal) := by
      simpa only [separatedNetCoverConstant, ENNReal.coe_pow, ENNReal.coe_ofNat,
        Nat.cast_pow, Nat.cast_ofNat] using
        (ENNReal.pow_le_pow_left (by norm_num : (3 : ENNReal) ≤ 5) :
          (3 : ENNReal) ^ Module.finrank ℝ E ≤ 5 ^ Module.finrank ℝ E)
    calc
      volume S' ≤ (((3 : NNReal) ^ Module.finrank ℝ E : NNReal) : ENNReal) *
          volume (S' ∩ ball y r) := hV
      _ ≤ (((3 : NNReal) ^ Module.finrank ℝ E : NNReal) : ENNReal) *
          volume (S ∩ ball y r) := by
        gcongr
      _ ≤ (separatedNetCoverConstant (Module.finrank ℝ E) : ENNReal) *
          volume (S ∩ ball y r) := by
        gcongr
  · rw [MeasureTheory.Measure.addHaar_ball_center volume y r,
        MeasureTheory.Measure.addHaar_ball_center volume x₀ r]

end Balls

end Kakeya

namespace ShadedBody

open MeasureTheory Set

/-- **A shaded point is shaded at the coarse scale** (blueprint `lem:ml2coarseShaded`).

If `x` lies in the shaded union `U(𝕋, Y')` of the inner family of a shaded factor family then
it lies in the shaded union `U(𝕋_a, Y_{𝕋_a})` of the outer family. This is exactly the
`shade_subset_parent` field, the blueprint's `pointwiseContainmenttube`, read at the level of
unions: the parent of a shaded index is an outer index, and it inherits the shade. -/
theorem mem_iUnion_outerShade_of_mem_iUnion_innerShade {E : Type*} [TopologicalSpace E]
    [MeasurableSpace E] [Convexity.ConvexSpace ℝ E] {ι κ : Type*}
    (G : ShadedFactorFamily E ι κ) {x : E}
    (hx : x ∈ ⋃ i ∈ G.innerSet, (G.innerBody i).shade) :
    x ∈ ⋃ j ∈ G.outerSet, (G.outerBody j).shade := by
  rcases Set.mem_iUnion₂.mp hx with ⟨i, hi, hxi⟩
  exact Set.mem_biUnion (G.parent_mem i hi) (G.shade_subset_parent i hi hxi)

end ShadedBody

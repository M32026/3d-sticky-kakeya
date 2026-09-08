/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.CanonicalCapsulesFibre
public import Kakeya.DimensionThree.MainLemma2.BallCoreOfCover
public import Kakeya.DimensionThree.MainLemma2.EDConstants

/-!
# C7-b, the dilation clause for the net capsules 

The field `Kakeya.VeryNotSticky.BallData.segs_dilation` asks, per ball,
`r₁² · Δ_max(𝕋_B) ≤ C_dil · Δ_max(𝕋)` (GWZ `gwz.txt` l.2209–2212), and the general contract pins
`C_dil = Kakeya.VeryNotSticky.segsDilationConstant` (`BallCoreOfCover.lean:154`, `3·2¹⁵/c₃`).  The
existing proof `ofReal_sq_mul_densityIn_le_of_segCarrierSet` is for T3's segments — one per parent,
inside the parent, window at the near end — and counts parents by `par`-injectivity.  The net
capsules (`CanonicalCapsules.lean`) are on **net** lines, contain the pieces of **several** parents
(a fibre), and are two-sided about the foot; this leaf is their twin:

* `capsuleAtBody` — the capsule as a `ConvexSpaceBody` (it is a `segCarrierSet`);
* `CapsuleNet.ofReal_sq_mul_densityIn_capsuleAt_le` — for every convex body `K`,
  `(4L)² · Δ(capsules, K) ≤ C_dil · Δ_max(𝕋)`, given the one product inequality `hC` that defines
  the constant.  The count replaces `par`-injectivity by the **disjoint fibres**: the capsules
  inside `K` have pairwise disjoint, nonempty fibres (`Finset.card_le_card_biUnion`), and every
  parent of such a capsule lies in the homothety container of `K`
  (`Convex.exists_homothety_container` at ratio `μ`, with `1 + L ≤ μL` and `fibreRadius ≤ μρ`:
  the parent's core point `foot + s•d`, `|s| ≤ 1 + L`, is `μ` times the capsule's core point at
  `s/μ`);
* `CapsuleNet.ofReal_sq_mul_maxDensity_capsuleAt_le` — the `Δ_max` form;
* **the measurement**: at the producer's parameters `ρ = 2δ`, `ε = δ`, `μ = (1+L)/L`, `L ≤ 1/4`,
  `4δ ≤ L` (i.e. `L = r₁/4`, `δ ≤ r₁/16`), the product is `≤ 576000 · δ²`
  (`le_capsuleDilationConstant_mul`), so `C_dil = capsuleDilationConstant = max 1 (576000/c₃)`
  (the contract's ceiling, `MainLemma2/EDConstants.lean`) works, and
  **`capsuleDilationConstant ≤ 6 · segsDilationConstant`** (`576000 ≤ 6 · 98304 = 589824`) — but
  **not** `≤ segsDilationConstant` (`576000/98304 = 5.86`).  The two factors over T3 are the
  two-sided dilation (`(1+L)³ ≤ 125/64` in place of `1`) and the capsule radius `2δ` with the
  assignment slack (`8(L+ρ)ρ² ≤ 48Lδ²` in place of `16Lδ²`).  The resulting dilation ceiling is
  `bd.Cdil ≤ capsuleDilationConstant`, and the T3 producer sits under it by
  `segsDilationConstant_le_capsuleDilationConstant` (`BallDataGeneral.lean`).

Everything here is proved; nothing is left as an obligation.
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

namespace Kakeya.VeryNotSticky

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {δ : NNReal}

/-- **The capsule as a convex body** (it is a `segCarrierSet`). -/
noncomputable def capsuleAtBody (T : Tube δ E3) (c : E3) (ρ : NNReal) {L : ℝ} (hL : 0 ≤ L) :
    ConvexSpaceBody E3 where
  carrier := capsuleAt T c ρ L
  convex' := by
    unfold capsuleAt segCarrierSet
    exact ((convex_segment _ _).cthickening _).isConvexSet
  isCompact' := by
    unfold capsuleAt segCarrierSet
    exact isCompact_segment.cthickening
  nonempty' := segCarrierSet_nonempty _ c hL

@[simp] theorem capsuleAtBody_carrier (T : Tube δ E3) (c : E3) (ρ : NNReal) {L : ℝ} (hL : 0 ≤ L) :
    (capsuleAtBody T c ρ hL).carrier = capsuleAt T c ρ L := rfl

/-- The foot lies in the capsule. -/
theorem foot_mem_capsuleAt (T : Tube δ E3) (c : E3) (ρ : NNReal) {L : ℝ} (hL : 0 ≤ L)
    (hL1 : L ≤ 1 / 2) : foot T c ∈ capsuleAt T c ρ L := by
  have h := mem_capsuleAt_of_dist_le T c ρ hL hL1 (s := 0) (by simpa using hL)
    (x := foot T c) (by simp)
  simpa using h

/-- **Every parent of a capsule's fibre is a `μ`-homothety image, about the foot, of a point of
the capsule**, once `1 + L ≤ μL` and `fibreRadius ≤ μρ`. -/
theorem exists_mem_capsuleAt_smul_sub_add (T T' : Tube δ E3) (c : E3) {ε L r : ℝ} {ρ : NNReal}
    {μ : ℝ} (hL : 0 < L) (hL1 : L ≤ 1 / 2) (hr : r + (δ : ℝ) ≤ L) (hμ1 : 1 ≤ μ)
    (hμL : 1 + L ≤ μ * L) (hμρ : fibreRadius δ ε L ≤ μ * ρ)
    (hclose : ‖foot T c - foot T' c‖ + L * ‖T.direction - T'.direction‖ ≤ ε)
    (hmeet : (T.carrier ∩ ball c r).Nonempty) {y : E3} (hy : y ∈ T.carrier) :
    ∃ x ∈ capsuleAt T' c ρ L, μ • (x - foot T' c) + foot T' c = y := by
  have hμ0 : 0 < μ := lt_of_lt_of_le zero_lt_one hμ1
  obtain ⟨s, hs, hys⟩ := exists_core_param_of_meets T c hr hmeet hy
  -- the parent's core point is within `fibreRadius` of the net line's point at `s`
  have hdir : ‖T.direction - T'.direction‖ ≤ ε / L := by
    rw [le_div_iff₀ hL]
    linarith [norm_nonneg (foot T c - foot T' c)]
  have hfoot : ‖foot T c - foot T' c‖ ≤ ε := by
    linarith [mul_nonneg hL.le (norm_nonneg (T.direction - T'.direction))]
  have hys' : dist y (foot T' c + s • T'.direction) ≤ fibreRadius δ ε L := by
    calc dist y (foot T' c + s • T'.direction)
        ≤ dist y (foot T c + s • T.direction) +
          dist (foot T c + s • T.direction) (foot T' c + s • T'.direction) := dist_triangle _ _ _
      _ ≤ δ + (ε + (1 + L) * (ε / L)) := by
          refine add_le_add hys ?_
          rw [dist_eq_norm]
          have h : foot T c + s • T.direction - (foot T' c + s • T'.direction)
              = (foot T c - foot T' c) + s • (T.direction - T'.direction) := by module
          rw [h]
          calc ‖(foot T c - foot T' c) + s • (T.direction - T'.direction)‖
              ≤ ‖foot T c - foot T' c‖ + ‖s • (T.direction - T'.direction)‖ := norm_add_le _ _
            _ = ‖foot T c - foot T' c‖ + |s| * ‖T.direction - T'.direction‖ := by
                rw [norm_smul, Real.norm_eq_abs]
            _ ≤ ε + (1 + L) * (ε / L) := by gcongr
      _ = fibreRadius δ ε L := by
          unfold fibreRadius
          field_simp
          ring
  -- the pre-image under the homothety
  refine ⟨foot T' c + μ⁻¹ • (y - foot T' c), ?_, ?_⟩
  · refine mem_capsuleAt_of_dist_le T' c ρ hL.le hL1 (s := s / μ) ?_ ?_
    · rw [abs_div, abs_of_pos hμ0, div_le_iff₀ hμ0]
      exact hs.trans (hμL.trans_eq (mul_comm _ _))
    · have h : foot T' c + μ⁻¹ • (y - foot T' c) - (foot T' c + (s / μ) • T'.direction)
          = μ⁻¹ • (y - (foot T' c + s • T'.direction)) := by
        rw [div_eq_inv_mul, ← smul_smul]
        module
      rw [dist_eq_norm, h, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hμ0),
        ← dist_eq_norm, inv_mul_le_iff₀ hμ0]
      exact hys'.trans hμρ
  · rw [add_sub_cancel_left, smul_smul, mul_inv_cancel₀ hμ0.ne', one_smul, sub_add_cancel]

/-- **The dilation comparison for the net capsules of one ball, at a single convex body `K`**:
`(4L)² · Δ(capsules, K) ≤ C_dil · Δ_max(s)` for any `C_dil` satisfying the product inequality
`hC` (the constant's definition).  Hypotheses: the net's family `I ⊆ s` meets `ball c r`,
`r + δ ≤ L ≤ 1/2`, and the homothety ratio `μ ≥ 1` satisfies `1 + L ≤ μL`, `fibreRadius ≤ μρ`. -/
theorem CapsuleNet.ofReal_sq_mul_densityIn_capsuleAt_le {ι : Type*} {I : Finset ι}
    {T : ι → Tube δ E3} {c : E3} {L ε : ℝ} (𝒩 : CapsuleNet I T c L ε) {s : Finset ι}
    (hI : I ⊆ s) (hL : 0 < L) (hL1 : L ≤ 1 / 2) {r : ℝ} (hr : r + (δ : ℝ) ≤ L)
    (hmeet : ∀ i ∈ I, ((T i).carrier ∩ ball c r).Nonempty) {ρ : NNReal} {μ : ℝ} (hμ1 : 1 ≤ μ)
    (hμL : 1 + L ≤ μ * L) (hμρ : fibreRadius δ ε L ≤ μ * ρ) {Cdil : ENNReal}
    (hC : ENNReal.ofReal (4 * L) ^ 2 * (8 * (ENNReal.ofReal (L + ρ) * ρ * ρ)) *
        (ENNReal.ofReal (4 * μ) ^ 3 * 6) ≤
      Cdil * ((Tube.le_volume.c 3 : ENNReal) * (δ : ENNReal) ^ 2))
    (K : ConvexSpaceBody E3) :
    ENNReal.ofReal (4 * L) ^ 2 * densityIn 𝒩.net (fun ν ↦ capsuleAtBody (T ν) c ρ hL.le) K ≤
      Cdil * maxDensity s (fun i ↦ (T i).toConvexSpaceBody) := by
  classical
  set Y' : ι → ConvexSpaceBody E3 := fun ν ↦ capsuleAtBody (T ν) c ρ hL.le with hY'
  set W : ι → ConvexSpaceBody E3 := fun i ↦ (T i).toConvexSpaceBody with hW
  by_cases hK0 : volume K.carrier = 0
  · rw [densityIn_eq_zero_of_volume_eq_zero hK0, mul_zero]
    exact zero_le
  have hKtop : volume K.carrier ≠ ⊤ := K.isCompact.measure_ne_top
  obtain ⟨D, hKD, hhom, hDvol⟩ := Convex.exists_homothety_container K.convex hK0 hKtop hμ1
  have h3 : ENNReal.ofReal (4 * μ) ^ Module.finrank ℝ E3 *
      ((Module.finrank ℝ E3).factorial : ENNReal) = ENNReal.ofReal (4 * μ) ^ 3 * 6 := by
    rw [finrank_euclideanSpace_fin]
    norm_num [Nat.factorial]
  rw [h3] at hDvol
  have hDne : volume D.carrier ≠ 0 :=
    (lt_of_lt_of_le (pos_iff_ne_zero.mpr hK0) (measure_mono hKD)).ne'
  have hDtop : volume D.carrier ≠ ⊤ := D.toConvexSpaceBody.isCompact.measure_ne_top
  -- the capsules inside `K`, and the union of their fibres
  set G : Finset ι := {ν ∈ 𝒩.net | Y' ν ≤ K} with hG
  have hGnet : G ⊆ 𝒩.net := Finset.filter_subset _ _
  set u : Finset ι := G.biUnion 𝒩.fibre with hu
  have hu_s : u ⊆ s := by
    rw [hu, Finset.biUnion_subset]
    intro ν _
    exact (𝒩.fibre_subset ν).trans hI
  have hpd : (𝒩.net : Set ι).PairwiseDisjoint 𝒩.fibre := 𝒩.fibre_disjoint
  have hGu : G.card ≤ u.card :=
    Finset.card_le_card_biUnion (hpd.subset (Finset.coe_subset.2 hGnet))
      (fun ν hν => ⟨ν, 𝒩.mem_fibre_self (hGnet hν)⟩)
  -- every parent of a capsule inside `K` lies in the container `D`
  have htube : ∀ i ∈ u, W i ≤ D.toConvexSpaceBody := by
    intro i hi
    obtain ⟨ν, hν, hiν⟩ := Finset.mem_biUnion.1 hi
    have hcapK : capsuleAt (T ν) c ρ L ⊆ K.carrier := (Finset.mem_filter.1 hν).2
    rw [← SetLike.coe_subset_coe]
    intro y hy
    obtain ⟨x, hx, rfl⟩ := exists_mem_capsuleAt_smul_sub_add (T i) (T ν) c hL hL1 hr hμ1 hμL
      hμρ (le_of_lt (𝒩.close_of_mem_fibre hiν)) (hmeet i (𝒩.fibre_subset ν hiν)) hy
    exact hhom _ (hcapK (foot_mem_capsuleAt (T ν) c ρ hL.le hL1)) _ (hcapK hx)
  have hvmin : ∀ i ∈ u, (Tube.le_volume.c 3 : ENNReal) * (δ : ENNReal) ^ 2 ≤
      volume (W i).carrier := by
    intro i _
    have h := Tube.le_volume (T i)
    rw [finrank_euclideanSpace_fin] at h
    simpa using h
  have hlow := densityIn_ge_of_count_volume hu_s htube hvmin
  -- the capsules inside `K` have volume `≤ 8 (L + ρ) ρ²`
  have hup : ∑ ν ∈ G, volume (Y' ν).carrier ≤
      (G.card : ENNReal) * (8 * (ENNReal.ofReal (L + ρ) * ρ * ρ)) := by
    rw [← nsmul_eq_mul]
    refine Finset.sum_le_card_nsmul _ _ _ fun ν _ ↦ ?_
    exact volume_segCarrierSet_le (centredTube (T ν) c ρ) c hL.le
  have hsum : ∑ ν ∈ G, volume (Y' ν).carrier = densityIn 𝒩.net Y' K * volume K.carrier :=
    sum_volume_eq_densityIn_mul_volume 𝒩.net Y' K
  have hGu' : (G.card : ENNReal) ≤ (u.card : ENNReal) := by exact_mod_cast hGu
  rw [← ENNReal.mul_le_mul_iff_left hK0 hKtop, ← ENNReal.mul_le_mul_iff_left hDne hDtop]
  calc ENNReal.ofReal (4 * L) ^ 2 * densityIn 𝒩.net Y' K * volume K.carrier * volume D.carrier
      = ENNReal.ofReal (4 * L) ^ 2 * (densityIn 𝒩.net Y' K * volume K.carrier) *
          volume D.carrier := by ring
    _ = ENNReal.ofReal (4 * L) ^ 2 * (∑ ν ∈ G, volume (Y' ν).carrier) * volume D.carrier := by
        rw [hsum]
    _ ≤ ENNReal.ofReal (4 * L) ^ 2 *
          ((G.card : ENNReal) * (8 * (ENNReal.ofReal (L + ρ) * ρ * ρ))) *
          (ENNReal.ofReal (4 * μ) ^ 3 * 6 * volume K.carrier) := by gcongr
    _ ≤ ENNReal.ofReal (4 * L) ^ 2 *
          ((u.card : ENNReal) * (8 * (ENNReal.ofReal (L + ρ) * ρ * ρ))) *
          (ENNReal.ofReal (4 * μ) ^ 3 * 6 * volume K.carrier) := by gcongr
    _ = (u.card : ENNReal) * (ENNReal.ofReal (4 * L) ^ 2 *
          (8 * (ENNReal.ofReal (L + ρ) * ρ * ρ)) * (ENNReal.ofReal (4 * μ) ^ 3 * 6)) *
          volume K.carrier := by ring
    _ ≤ (u.card : ENNReal) * (Cdil * ((Tube.le_volume.c 3 : ENNReal) * (δ : ENNReal) ^ 2)) *
          volume K.carrier := by gcongr
    _ = Cdil * ((u.card : ENNReal) * ((Tube.le_volume.c 3 : ENNReal) * (δ : ENNReal) ^ 2) /
          volume D.carrier * volume D.carrier) * volume K.carrier := by
        rw [ENNReal.div_mul_cancel hDne hDtop]; ring
    _ ≤ Cdil * (densityIn s W D.toConvexSpaceBody * volume D.carrier) * volume K.carrier := by
        gcongr
    _ ≤ Cdil * (maxDensity s W * volume D.carrier) * volume K.carrier := by
        gcongr
        exact le_maxDensity s W D.toConvexSpaceBody
    _ = Cdil * maxDensity s W * volume K.carrier * volume D.carrier := by ring

/-- **The `Δ_max` form**: `(4L)² · Δ_max(capsules) ≤ C_dil · Δ_max(s)`. -/
theorem CapsuleNet.ofReal_sq_mul_maxDensity_capsuleAt_le {ι : Type*} {I : Finset ι}
    {T : ι → Tube δ E3} {c : E3} {L ε : ℝ} (𝒩 : CapsuleNet I T c L ε) {s : Finset ι}
    (hI : I ⊆ s) (hL : 0 < L) (hL1 : L ≤ 1 / 2) {r : ℝ} (hr : r + (δ : ℝ) ≤ L)
    (hmeet : ∀ i ∈ I, ((T i).carrier ∩ ball c r).Nonempty) {ρ : NNReal} {μ : ℝ} (hμ1 : 1 ≤ μ)
    (hμL : 1 + L ≤ μ * L) (hμρ : fibreRadius δ ε L ≤ μ * ρ) {Cdil : ENNReal}
    (hC : ENNReal.ofReal (4 * L) ^ 2 * (8 * (ENNReal.ofReal (L + ρ) * ρ * ρ)) *
        (ENNReal.ofReal (4 * μ) ^ 3 * 6) ≤
      Cdil * ((Tube.le_volume.c 3 : ENNReal) * (δ : ENNReal) ^ 2)) :
    ENNReal.ofReal (4 * L) ^ 2 * maxDensity 𝒩.net (fun ν ↦ capsuleAtBody (T ν) c ρ hL.le) ≤
      Cdil * maxDensity s (fun i ↦ (T i).toConvexSpaceBody) := by
  rw [← densityIn_self_maximizer_eq]
  exact 𝒩.ofReal_sq_mul_densityIn_capsuleAt_le hI hL hL1 hr hmeet hμ1 hμL hμρ hC _

/-! ### The measurement (B3): the constant at the producer's parameters

The constant itself, `Kakeya.VeryNotSticky.capsuleDilationConstant = max 1 (576000 / c₃)`, is
the contract's dilation ceiling and lives in `MainLemma2/EDConstants.lean`;
`1 ≤ capsuleDilationConstant` is `one_le_capsuleDilationConstant` there, and
`segsDilationConstant ≤ capsuleDilationConstant` is
`segsDilationConstant_le_capsuleDilationConstant` in `BallDataGeneral.lean`.  At `ρ = 2δ`,
`ε = δ`, `μ = (1+L)/L`, `L ≤ 1/4`, `4δ ≤ L` the product of
`CapsuleNet.ofReal_sq_mul_densityIn_capsuleAt_le`'s `hC` is
`2¹⁶·3 · (1 + 2δ/L)(1 + L)³ · δ² ≤ 2¹⁶·3 · (3/2)(125/64) · δ² = 576000 · δ²`.  Compare
`segsDilationConstant = max 1 (3·2¹⁵/c₃) = max 1 (98304/c₃)`: this is `5.86×` larger
(`capsuleDilationConstant_le_six_mul_segsDilationConstant`). -/

/-- The real inequality behind the constant. -/
theorem capsule_dilation_product_le {L d : ℝ} (hL : 0 < L) (hL4 : L ≤ 1 / 4) (hd : 0 ≤ d)
    (hδL : 4 * d ≤ L) :
    (4 * L) ^ 2 * (8 * ((L + 2 * d) * (2 * d) * (2 * d))) * ((4 * ((1 + L) / L)) ^ 3 * 6) ≤
      576000 * d ^ 2 := by
  have h1 : L + 2 * d ≤ 3 / 2 * L := by linarith
  have h2 : (1 + L) ^ 3 ≤ 125 / 64 := by
    have : 1 + L ≤ 5 / 4 := by linarith
    calc (1 + L) ^ 3 ≤ (5 / 4 : ℝ) ^ 3 := by gcongr
      _ = 125 / 64 := by norm_num
  have hkey : (L + 2 * d) * (1 + L) ^ 3 ≤ 375 / 128 * L := by
    calc (L + 2 * d) * (1 + L) ^ 3 ≤ (3 / 2 * L) * (125 / 64) := by
          gcongr
        _ = 375 / 128 * L := by ring
  have hexp : (4 * L) ^ 2 * (8 * ((L + 2 * d) * (2 * d) * (2 * d))) *
      ((4 * ((1 + L) / L)) ^ 3 * 6) = 196608 * ((L + 2 * d) * (1 + L) ^ 3 / L) * d ^ 2 := by
    field_simp
    ring
  rw [hexp]
  have : (L + 2 * d) * (1 + L) ^ 3 / L ≤ 375 / 128 := by
    rw [div_le_iff₀ hL]
    exact hkey
  calc 196608 * ((L + 2 * d) * (1 + L) ^ 3 / L) * d ^ 2
      ≤ 196608 * (375 / 128) * d ^ 2 := by gcongr
    _ = 576000 * d ^ 2 := by norm_num

/-- **The `hC` of the dilation theorem at the producer's parameters** (`ρ = 2δ`, `μ = (1+L)/L`,
`L ≤ 1/4`, `4δ ≤ L`), with `C_dil = capsuleDilationConstant`. -/
theorem le_capsuleDilationConstant_mul {L : ℝ} (hL : 0 < L) (hL4 : L ≤ 1 / 4)
    (hδL : 4 * (δ : ℝ) ≤ L) :
    ENNReal.ofReal (4 * L) ^ 2 *
        (8 * (ENNReal.ofReal (L + ((2 * δ : NNReal) : ℝ)) * ((2 * δ : NNReal) : ENNReal) *
          ((2 * δ : NNReal) : ENNReal))) * (ENNReal.ofReal (4 * ((1 + L) / L)) ^ 3 * 6) ≤
      (capsuleDilationConstant : ENNReal) *
        ((Tube.le_volume.c 3 : ENNReal) * (δ : ENNReal) ^ 2) := by
  have hd : (0 : ℝ) ≤ (δ : ℝ) := δ.coe_nonneg
  have hc : 0 < Tube.le_volume.c 3 := Tube.le_volume.c_pos 3
  -- the left side as `ofReal` of a real
  have hlhs : ENNReal.ofReal (4 * L) ^ 2 *
      (8 * (ENNReal.ofReal (L + ((2 * δ : NNReal) : ℝ)) * ((2 * δ : NNReal) : ENNReal) *
        ((2 * δ : NNReal) : ENNReal))) * (ENNReal.ofReal (4 * ((1 + L) / L)) ^ 3 * 6) =
      ENNReal.ofReal ((4 * L) ^ 2 * (8 * ((L + 2 * (δ : ℝ)) * (2 * (δ : ℝ)) * (2 * (δ : ℝ)))) *
        ((4 * ((1 + L) / L)) ^ 3 * 6)) := by
    have h2δ : ((2 * δ : NNReal) : ENNReal) = ENNReal.ofReal (2 * (δ : ℝ)) := by
      rw [← ENNReal.ofReal_coe_nnreal]; push_cast; rfl
    have h2δ' : ((2 * δ : NNReal) : ℝ) = 2 * (δ : ℝ) := by push_cast; rfl
    have hA : (0 : ℝ) ≤ (4 * L) ^ 2 := by positivity
    have hB : (0 : ℝ) ≤ 8 * ((L + 2 * (δ : ℝ)) * (2 * (δ : ℝ)) * (2 * (δ : ℝ))) := by positivity
    have hAB : (0 : ℝ) ≤
        (4 * L) ^ 2 * (8 * ((L + 2 * (δ : ℝ)) * (2 * (δ : ℝ)) * (2 * (δ : ℝ)))) := by
      positivity
    have hB1 : (0 : ℝ) ≤ (L + 2 * (δ : ℝ)) * (2 * (δ : ℝ)) := by positivity
    have hB0 : (0 : ℝ) ≤ L + 2 * (δ : ℝ) := by positivity
    have hC3 : (0 : ℝ) ≤ (4 * ((1 + L) / L)) ^ 3 := by positivity
    symm
    rw [ENNReal.ofReal_mul hAB, ENNReal.ofReal_mul hA,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8),
      ENNReal.ofReal_mul hB1, ENNReal.ofReal_mul hB0, ENNReal.ofReal_mul hC3,
      ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ 4 * L),
      ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ 4 * ((1 + L) / L)),
      ENNReal.ofReal_ofNat, ENNReal.ofReal_ofNat, h2δ, h2δ']
  -- the right side is at least `576000 · δ²`
  have hrhs : ENNReal.ofReal (576000 * (δ : ℝ) ^ 2) ≤
      (capsuleDilationConstant : ENNReal) *
        ((Tube.le_volume.c 3 : ENNReal) * (δ : ENNReal) ^ 2) := by
    have h1 : (576000 : NNReal) ≤ capsuleDilationConstant * Tube.le_volume.c 3 := by
      calc (576000 : NNReal) = 576000 / Tube.le_volume.c 3 * Tube.le_volume.c 3 :=
            (div_mul_cancel₀ _ hc.ne').symm
        _ ≤ capsuleDilationConstant * Tube.le_volume.c 3 :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) zero_le
    have h1' : ((576000 : NNReal) : ENNReal) ≤
        (capsuleDilationConstant : ENNReal) * (Tube.le_volume.c 3 : ENNReal) := by
      exact_mod_cast h1
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow hd, ENNReal.ofReal_coe_nnreal,
      ENNReal.ofReal_ofNat, ← mul_assoc]
    gcongr
    simpa using h1'
  rw [hlhs]
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) hrhs
  exact capsule_dilation_product_le hL hL4 hd hδL

/-- **The measurement, compiled**: the capsule dilation constant is at most six times the existing
`segsDilationConstant` (`576000 ≤ 6 · 98304 = 589824`). -/
theorem capsuleDilationConstant_le_six_mul_segsDilationConstant :
    capsuleDilationConstant ≤ 6 * segsDilationConstant := by
  unfold capsuleDilationConstant segsDilationConstant
  have hc : 0 < Tube.le_volume.c 3 := Tube.le_volume.c_pos 3
  refine max_le ?_ ?_
  · calc (1 : NNReal) ≤ 6 * 1 := by norm_num
      _ ≤ 6 * max 1 (3 * 2 ^ 15 / Tube.le_volume.c 3) := by gcongr; exact le_max_left _ _
  · calc (576000 : NNReal) / Tube.le_volume.c 3 ≤ 6 * (3 * 2 ^ 15 / Tube.le_volume.c 3) := by
          rw [← mul_div_assoc]
          gcongr
          norm_num
      _ ≤ 6 * max 1 (3 * 2 ^ 15 / Tube.le_volume.c 3) := by gcongr; exact le_max_right _ _

/-- The ratio, as a record: the constant `576000` is `5.859…` times the existing `3·2¹⁵ = 98304`,
i.e. **the net capsules do not fit under `segsDilationConstant` as pinned** (`98304 < 576000`).
Stated on the numerators, which is where the two constants differ. -/
theorem segsDilation_numerator_lt_capsule_numerator : (3 * 2 ^ 15 : ℕ) < 576000 := by
  norm_num

end Kakeya.VeryNotSticky

end

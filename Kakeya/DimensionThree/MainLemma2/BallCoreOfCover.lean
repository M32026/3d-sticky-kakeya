/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.SetupIslandCut
public import Kakeya.DimensionThree.MainLemma2.BallJoint
public import Kakeya.Thickness.BoundingBox

/-!
# The core of `BallData` from a given ball cover, and the dilation clause for its capsules

Two items of the side-data construction plan.

* `Kakeya.VeryNotSticky.ballDataCoreOfCover` is the body of
  `Kakeya.VeryNotSticky.exists_ballDataCore` with its internal call to
  `Kakeya.VeryNotSticky.exists_ballCover` replaced by a **given** `r₁`-ball cover of the
  configuration's shadings — the eight clauses `exists_ballCover` (equivalently, T1's
  `Kakeya.VeryNotSticky.exists_ballCover_family`) produces. It is a `def` rather than an
  existential so that its segment family stays visible: the segments are the capsules
  `Kakeya.VeryNotSticky.segShadedBody` of half-length `r₁/4` along the parent tubes, one per
  pair (tube, piece), with singleton parent families. `exists_ballDataCore_of_cover` is the
  `Nonempty` form.

* `Kakeya.VeryNotSticky.segs_dilation_capsules` is the honest dilation clause
  `r₁² Δ_max(𝕋_B) ≤ C_dil Δ_max(𝕋)` for any
  `BallDataCore` whose segments are such capsules, at the **explicit dimensional constant**
  `Kakeya.VeryNotSticky.segsDilationConstant = 3 · 2¹⁵ / c₃`, `c₃ = Tube.le_volume.c 3`. This is
  the producer that `Kakeya/DimensionThree/MainLemma2/BallJoint.lean` (docstring of
  `segs_dilation_of_maxDensity_le`) said "a successor has to work" for: the absolute bound
  `Δ_max(𝕋_B) ≤ r₁^{-2}` used there is unavailable for `C₀`-comparable capsules.

## The dilation argument, made honest

GWZ write: "each tube `T_B ∈ 𝕋_B` is contained in a tube `T ∈ 𝕋`. If `T_B ⊂ K`, then the
corresponding tube `T` is contained in `r₁⁻¹ K`, the dilation of `K` by a factor `r₁⁻¹`.
Therefore `Δ_max(𝕋_B) ≤ r₁⁻² Δ_max(𝕋)`." Read literally with a *fixed* centre this is false: the
segments of `K` have different midpoints, and the homothety of `K` about one of them does not
contain the parent tube of another (a unit segment through a point at distance `∼ r₁` from
the centre, transversal to the ray, leaves the cone). What is true, and what is proved here:

* the parent tube `T` of a segment `T_B = N_δ([z₁, z₂])` (core window of length `2L = r₁/2`)
  is contained in the image of `T_B` under the homothety of ratio `L⁻¹ = 4/r₁` about the
  **window midpoint** `m` of that segment
  (`Kakeya.VeryNotSticky.exists_mem_segCarrierSet_inv_smul_sub_add`);
* `Convex.exists_homothety_container` (`Kakeya/Thickness/BoundingBox.lean`) gives a single
  prism `D ⊇ K` containing `λ(x - p) + p` for **all** `p, x ∈ K`, of volume
  `≤ (4λ)³ · 3! · |K|` — the bounding box of `K` absorbs the moving centre;
* so every parent of a segment inside `K` lies in `D`, the parents are distinct
  (`fam_disjoint`), each has volume `≥ c₃ δ²` (`Tube.le_volume`) while each segment has volume
  `≤ 8 (L + δ) δ² ≤ 4 · (4L) δ²` (`Kakeya.VeryNotSticky.volume_segCarrierSet_le`), and the chain
  `r₁² Δ(𝕋_B, K) ≤ r₁² · #·4 r₁ δ² / |K| ≤ 3·2¹⁵/c₃ · #·c₃δ²/|D| ≤ C_dil Δ(𝕋, D) ≤ C_dil Δ_max(𝕋)`
  closes with `r₁ = 4L` and `|D| ≤ (16/r₁)³ · 6 |K|`.

The constant is dimensional: it depends on nothing but the ambient dimension `3` (through the
bounding-box constants `4³ · 3!`, the capsule volume constant `8 · 2 = 16`, and the tube volume
constant `c₃`). In particular it does **not** depend on `δ`, `r₁`, or the family.
-/

@[expose] public section

namespace Kakeya.VeryNotSticky

open MeasureTheory Metric Set ShadedBody

universe u

/-! ### The dilation geometry of a capsule -/

section CapsuleDilation

variable {δ : NNReal}

/-- **The window midpoint lies in the segment.** -/
lemma corePt_segStart_add_mem_segCarrierSet (T : Tube δ (EuclideanSpace ℝ (Fin 3)))
    (c : EuclideanSpace ℝ (Fin 3)) {L : ℝ} (hL : 0 ≤ L) :
    corePt T (segStart T c L + L) ∈ segCarrierSet T c L := by
  refine Metric.self_subset_cthickening _ ?_
  exact corePt_image_subset_segment T (by linarith)
    ⟨segStart T c L + L, ⟨by linarith, by linarith⟩, rfl⟩

/-- **Every point of a tube is a homothety image of a point of any of its segments**, the
homothety being of ratio `L⁻¹` about the window midpoint `m = corePt T (segStart + L)` of the
segment: `y = L⁻¹ • (x - m) + m` with `x ∈ N_δ([z₁, z₂])`.

This is the honest form of GWZ's "`T ⊂ r₁⁻¹ K`" (`gwz.txt` l.2210–2211): the core window has
half-length `L`, the whole core has length `1 ≤ L⁻¹ · L`, and the `δ`-neighbourhood scales by
`L⁻¹ ≥ 1`. The centre is the segment's own midpoint, not a fixed point of `K`. -/
lemma exists_mem_segCarrierSet_inv_smul_sub_add (T : Tube δ (EuclideanSpace ℝ (Fin 3)))
    (c : EuclideanSpace ℝ (Fin 3)) {L : ℝ} (hL : 0 < L) (hL1 : 2 * L ≤ 1)
    {y : EuclideanSpace ℝ (Fin 3)} (hy : y ∈ T.carrier) :
    ∃ x ∈ segCarrierSet T c L,
      L⁻¹ • (x - corePt T (segStart T c L + L)) + corePt T (segStart T c L + L) = y := by
  have hs₀ : 0 ≤ segStart T c L := segStart_nonneg T c hL1
  have hs₁ : segStart T c L + 2 * L ≤ 1 := segStart_add_le_one T c
  rw [T.carrier_eq] at hy
  obtain ⟨w, hw, hyw⟩ := Set.mem_iUnion₂.mp hy
  obtain ⟨s, hs, rfl⟩ := exists_corePt_of_mem_core T hw
  rw [Metric.mem_closedBall] at hyw
  refine ⟨corePt T (segStart T c L + L) + L • (y - corePt T (segStart T c L + L)), ?_, ?_⟩
  · rw [segCarrierSet_eq_biUnion]
    refine Set.mem_iUnion₂.mpr
      ⟨corePt T (segStart T c L + L + L * (s - (segStart T c L + L))), ?_, ?_⟩
    · refine corePt_image_subset_segment T (by linarith) ⟨_, ⟨?_, ?_⟩, rfl⟩
      · nlinarith [hs.1, hs.2]
      · nlinarith [hs.1, hs.2]
    · have hpt : corePt T (segStart T c L + L + L * (s - (segStart T c L + L))) =
          corePt T (segStart T c L + L) + L • (corePt T s - corePt T (segStart T c L + L)) := by
        simp only [corePt]; module
      rw [Metric.mem_closedBall, hpt, dist_eq_norm]
      have hsub : corePt T (segStart T c L + L) + L • (y - corePt T (segStart T c L + L)) -
          (corePt T (segStart T c L + L) + L • (corePt T s - corePt T (segStart T c L + L))) =
          L • (y - corePt T s) := by module
      rw [hsub, norm_smul, Real.norm_of_nonneg hL.le, ← dist_eq_norm]
      calc L * dist y (corePt T s) ≤ 1 * (δ : ℝ) := by
            gcongr
            linarith
        _ = (δ : ℝ) := one_mul _
  · rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hL.ne', one_smul, sub_add_cancel]

/-- **The volume of a segment**: `|N_δ([z₁, z₂])| ≤ 8 (L + δ) δ² ≤ 16 L δ² = 4 · (4L) · δ²` once
`δ ≤ L`, from `Kakeya.VeryNotSticky.volume_segCarrierSet_le`. Stated with `4L` because the
segments of the construction have `4L = r₁`. -/
lemma volume_segCarrierSet_le_four_mul (T : Tube δ (EuclideanSpace ℝ (Fin 3)))
    (c : EuclideanSpace ℝ (Fin 3)) {L : ℝ} (hL : 0 ≤ L) (hδL : (δ : ℝ) ≤ L) :
    volume (segCarrierSet T c L) ≤ 4 * ENNReal.ofReal (4 * L) * (δ : ENNReal) ^ 2 := by
  refine (volume_segCarrierSet_le T c hL).trans ?_
  have h2 : ENNReal.ofReal (L + (δ : ℝ)) ≤ ENNReal.ofReal (2 * L) :=
    ENNReal.ofReal_le_ofReal (by linarith)
  calc 8 * (ENNReal.ofReal (L + (δ : ℝ)) * (δ : ENNReal) * (δ : ENNReal))
      ≤ 8 * (ENNReal.ofReal (2 * L) * (δ : ENNReal) * (δ : ENNReal)) := by gcongr
    _ = 4 * ENNReal.ofReal (4 * L) * (δ : ENNReal) ^ 2 := by
        rw [show (4 : ℝ) * L = 2 * (2 * L) by ring, ENNReal.ofReal_mul (by norm_num)]
        norm_num
        ring

end CapsuleDilation

/-! ### The dilation constant -/

/-- **The dilation constant of the capsule segments**: `C_dil = 3 · 2¹⁵ / c₃` with
`c₃ = Tube.le_volume.c 3` the tube volume constant (`c₃ δ² ≤ |T|`), capped below by `1`.

Where the factors come from: a segment has volume `≤ 8 (L + δ) δ² ≤ 4 · (4L) δ²`
(`Kakeya.VeryNotSticky.volume_segCarrierSet_le` with `δ ≤ L`), the homothety container of a
convex `K` at ratio `λ = 1/L` has volume `≤ (4λ)³ · 3! · |K|`, and `r₁ = 4L`; so
`r₁² · [4 · 4L δ²] · (4/L)³ · 6 = 4 · 6 · 16³ · δ² = 3 · 2¹⁵ δ²` is paid for by
`C_dil · c₃ δ²`. The cap makes `1 ≤ C_dil` (the field `Kakeya.VeryNotSticky.BallData.hCdil`)
available without an upper bound on `c₃`. The constant depends only on the dimension. -/
noncomputable def segsDilationConstant : NNReal :=
  max 1 (3 * 2 ^ 15 / Tube.le_volume.c 3)

theorem one_le_segsDilationConstant : 1 ≤ segsDilationConstant := le_max_left _ _

/-- The defining inequality of `segsDilationConstant`: `3 · 2¹⁵ ≤ C_dil · c₃`. -/
theorem le_segsDilationConstant_mul :
    (3 * 2 ^ 15 : ENNReal) ≤
      (segsDilationConstant : ENNReal) * ((Tube.le_volume.c 3 : NNReal) : ENNReal) := by
  have hc : Tube.le_volume.c 3 ≠ 0 := (Tube.le_volume.c_pos 3).ne'
  have h : (3 * 2 ^ 15 : NNReal) ≤ segsDilationConstant * Tube.le_volume.c 3 := by
    calc (3 * 2 ^ 15 : NNReal) = 3 * 2 ^ 15 / Tube.le_volume.c 3 * Tube.le_volume.c 3 :=
          (div_mul_cancel₀ _ hc).symm
      _ ≤ segsDilationConstant * Tube.le_volume.c 3 :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) zero_le
  have h' := ENNReal.coe_le_coe.mpr h
  rw [ENNReal.coe_mul] at h'
  simpa using h'

/-! ### The dilation clause for a family of capsules -/

section CapsuleDensity

variable {δ : NNReal}

/-- **The dilation comparison for a family of capsules along distinct parent tubes**, at a
single convex body `K`: if the members of `t` are the capsules of half-length `L` (window
midpoints anywhere) along the tubes `T (par p)`, `par` injective on `t` with values in `s`,
then `(4L)² Δ(t, K) ≤ C_dil Δ_max(s)`.

This is GWZ `gwz.txt` l.2209–2212 with the dilation taken about each segment's own midpoint
and the moving centres absorbed by the bounding-box container
`Convex.exists_homothety_container`. -/
theorem ofReal_sq_mul_densityIn_le_of_segCarrierSet {ι σ : Type*} (s : Finset ι)
    (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (t : Finset σ)
    (Y : σ → ShadedBody (EuclideanSpace ℝ (Fin 3))) (par : σ → ι)
    (hpar : ∀ p ∈ t, par p ∈ s) (hinj : Set.InjOn par (t : Set σ))
    (c : EuclideanSpace ℝ (Fin 3)) {L : ℝ} (hL : 0 < L) (hL1 : 2 * L ≤ 1)
    (hδL : (δ : ℝ) ≤ L)
    (hcar : ∀ p ∈ t, (Y p).carrier = segCarrierSet (T (par p)).toTube c L)
    (K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) :
    ENNReal.ofReal (4 * L) ^ 2 * densityIn t (fun p ↦ (Y p).toConvexSpaceBody) K ≤
      (segsDilationConstant : ENNReal) * maxDensity s (fun i ↦ (T i).toConvexSpaceBody) := by
  classical
  set Y' : σ → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) := fun p ↦ (Y p).toConvexSpaceBody
    with hY'
  set T' : ι → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) := fun i ↦ (T i).toConvexSpaceBody
    with hT'
  -- the degenerate case: `K` null
  by_cases hK0 : volume K.carrier = 0
  · rw [densityIn_eq_zero_of_volume_eq_zero hK0, mul_zero]
    exact zero_le
  have hKtop : volume K.carrier ≠ ⊤ := K.isCompact.measure_ne_top
  have hLinv : (1 : ℝ) ≤ L⁻¹ := (one_le_inv₀ hL).mpr (by linarith)
  -- the container of all homothety images of `K` about its own points
  obtain ⟨D, hKD, hhom, hDvol⟩ :=
    Convex.exists_homothety_container K.convex hK0 hKtop hLinv
  have h3 : ENNReal.ofReal (4 * L⁻¹) ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) *
      ((Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))).factorial : ENNReal) =
      ENNReal.ofReal (4 * L⁻¹) ^ 3 * 6 := by
    rw [finrank_euclideanSpace_fin]
    norm_num [Nat.factorial]
  rw [h3] at hDvol
  have hDne : volume D.carrier ≠ 0 :=
    (lt_of_lt_of_le (pos_iff_ne_zero.mpr hK0) (measure_mono hKD)).ne'
  have hDtop : volume D.carrier ≠ ⊤ := D.toConvexSpaceBody.isCompact.measure_ne_top
  -- the segments inside `K` and their parents
  set t₁ : Finset σ := {p ∈ t | Y' p ≤ K} with ht₁
  have ht₁t : t₁ ⊆ t := Finset.filter_subset _ _
  set u : Finset ι := t₁.image par with hu
  have hu_s : u ⊆ s := by
    intro i hi
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hi
    exact hpar p (ht₁t hp)
  have hu_card : u.card = t₁.card :=
    Finset.card_image_of_injOn (hinj.mono (by exact_mod_cast ht₁t))
  -- every parent of a segment inside `K` lies in the container `D`
  have htube : ∀ i ∈ u, T' i ≤ D.toConvexSpaceBody := by
    intro i hi
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hi
    have hpt : p ∈ t := ht₁t hp
    have hpK : (Y p).carrier ⊆ K.carrier := (Finset.mem_filter.1 hp).2
    rw [← SetLike.coe_subset_coe]
    intro y hy
    obtain ⟨x, hx, rfl⟩ :=
      exists_mem_segCarrierSet_inv_smul_sub_add (T (par p)).toTube c hL hL1 hy
    have hm := corePt_segStart_add_mem_segCarrierSet (T (par p)).toTube c hL.le
    rw [← hcar p hpt] at hx hm
    exact hhom _ (hpK hm) _ (hpK hx)
  -- the parents have volume `≥ c₃ δ²`
  have hvmin : ∀ i ∈ u, ((Tube.le_volume.c 3 : NNReal) : ENNReal) * (δ : ENNReal) ^ 2 ≤
      volume (T' i).carrier := by
    intro i _
    have h := Tube.le_volume (T i).toTube
    rw [finrank_euclideanSpace_fin] at h
    exact h
  have hlow := densityIn_ge_of_count_volume hu_s htube hvmin
  rw [hu_card] at hlow
  -- the segments inside `K` have volume `≤ 4 · (4L) δ²`
  have hup : ∑ p ∈ t₁, volume (Y' p).carrier ≤
      (t₁.card : ENNReal) * (4 * ENNReal.ofReal (4 * L) * (δ : ENNReal) ^ 2) := by
    rw [← nsmul_eq_mul]
    refine Finset.sum_le_card_nsmul _ _ _ fun p hp ↦ ?_
    change volume (Y p).carrier ≤ _
    rw [hcar p (ht₁t hp)]
    exact volume_segCarrierSet_le_four_mul _ c hL.le hδL
  have hsum : ∑ p ∈ t₁, volume (Y' p).carrier = densityIn t Y' K * volume K.carrier :=
    sum_volume_eq_densityIn_mul_volume t Y' K
  -- the product `ofReal (4L) · ofReal (4/L) = 16`
  have hab : ENNReal.ofReal (4 * L) * ENNReal.ofReal (4 * L⁻¹) = 16 := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    rw [show 4 * L * (4 * L⁻¹) = 16 * (L * L⁻¹) by ring, mul_inv_cancel₀ hL.ne', mul_one]
    norm_num
  -- assemble
  rw [← ENNReal.mul_le_mul_iff_left hK0 hKtop, ← ENNReal.mul_le_mul_iff_left hDne hDtop]
  calc ENNReal.ofReal (4 * L) ^ 2 * densityIn t Y' K * volume K.carrier * volume D.carrier
      = ENNReal.ofReal (4 * L) ^ 2 * (densityIn t Y' K * volume K.carrier) *
          volume D.carrier := by ring
    _ = ENNReal.ofReal (4 * L) ^ 2 * (∑ p ∈ t₁, volume (Y' p).carrier) *
          volume D.carrier := by rw [hsum]
    _ ≤ ENNReal.ofReal (4 * L) ^ 2 *
          ((t₁.card : ENNReal) * (4 * ENNReal.ofReal (4 * L) * (δ : ENNReal) ^ 2)) *
          (ENNReal.ofReal (4 * L⁻¹) ^ 3 * 6 * volume K.carrier) := by gcongr
    _ = (t₁.card : ENNReal) *
          (4 * 6 * (ENNReal.ofReal (4 * L) * ENNReal.ofReal (4 * L⁻¹)) ^ 3 *
            (δ : ENNReal) ^ 2) * volume K.carrier := by ring
    _ = (t₁.card : ENNReal) * ((3 * 2 ^ 15 : ENNReal) * (δ : ENNReal) ^ 2) *
          volume K.carrier := by rw [hab]; norm_num
    _ ≤ (t₁.card : ENNReal) * ((segsDilationConstant : ENNReal) *
          ((Tube.le_volume.c 3 : NNReal) : ENNReal) * (δ : ENNReal) ^ 2) *
          volume K.carrier := by
        gcongr (t₁.card : ENNReal) * (?_ * (δ : ENNReal) ^ 2) * volume K.carrier
        exact le_segsDilationConstant_mul
    _ = (segsDilationConstant : ENNReal) *
          ((t₁.card : ENNReal) * (((Tube.le_volume.c 3 : NNReal) : ENNReal) *
            (δ : ENNReal) ^ 2) / volume D.carrier * volume D.carrier) *
          volume K.carrier := by
        rw [ENNReal.div_mul_cancel hDne hDtop]; ring
    _ ≤ (segsDilationConstant : ENNReal) *
          (densityIn s T' D.toConvexSpaceBody * volume D.carrier) * volume K.carrier := by
        gcongr
    _ ≤ (segsDilationConstant : ENNReal) *
          (maxDensity s T' * volume D.carrier) * volume K.carrier := by
        gcongr
        exact le_maxDensity s T' D.toConvexSpaceBody
    _ = (segsDilationConstant : ENNReal) * maxDensity s T' * volume K.carrier *
          volume D.carrier := by ring

end CapsuleDensity

/-! ### The dilation clause for a `BallDataCore` whose segments are capsules -/

/-- **The honest `segs_dilation` clause for capsule segments** (GWZ `gwz.txt` l.2209–2212; the
field `Kakeya.VeryNotSticky.BallData.segs_dilation` at the constant
`Kakeya.VeryNotSticky.segsDilationConstant`).

For a `BallDataCore` whose segments are the capsules of half-length `r₁/4` along parent tubes
— `par p ∈ fam p` and `(Y p).carrier = segCarrierSet (T (par p)) (ctr B) (r₁/4)` for every
`p ∈ segs B` — the segment family of every ball satisfies
`r₁² Δ_max(𝕋_B) ≤ C_dil Δ_max(𝕋)`. The parents of distinct segments are distinct by
`fam_disjoint`, and lie in `𝕋` by `fam_subset`; the scale hypothesis `16δ ≤ r₁` is the one
`Kakeya.VeryNotSticky.exists_ballDataCore` already carries (it gives `δ ≤ r₁/4`).

This is exactly the hypothesis `hdil` of
`Kakeya.VeryNotSticky.BallDataCore.nonempty_ballData_of_dilation` at `Cdil := segsDilationConstant`
(with `Kakeya.VeryNotSticky.one_le_segsDilationConstant` for `hCdil`), and the segments of
`Kakeya.VeryNotSticky.ballDataCoreOfCover` satisfy the capsule hypothesis with `par := Prod.fst`
(`Kakeya.VeryNotSticky.segs_dilation_ballDataCoreOfCover`). -/
theorem segs_dilation_capsules {cfg : VeryNotSticky.{u}} (core : BallDataCore cfg)
    (hδr : 16 * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ)) (par : core.σ → cfg.ι)
    (hpar : ∀ B ∈ core.bs, ∀ p ∈ core.segs B, par p ∈ core.fam p ∧
      (core.Y p).carrier =
        segCarrierSet (cfg.T (par p)).toTube (core.ctr B) ((cfg.r₁ : ℝ) / 4)) :
    ∀ B ∈ core.bs,
      (cfg.r₁ : ENNReal) ^ 2 *
          maxDensity (core.segs B) (fun p ↦ (core.Y p).toConvexSpaceBody) ≤
        (segsDilationConstant : ENNReal) *
          maxDensity cfg.s (fun i ↦ (cfg.T i).toConvexSpaceBody) := by
  intro B hB
  have hr₁pos : (0 : ℝ) < (cfg.r₁ : ℝ) := by exact_mod_cast NNReal.rpow_pos cfg.hδ
  have hr₁1 : (cfg.r₁ : ℝ) ≤ 1 := r₁_le_one cfg
  have hδ0 : (0 : ℝ) ≤ (cfg.δ : ℝ) := (cfg.δ).coe_nonneg
  have hL : (0 : ℝ) < (cfg.r₁ : ℝ) / 4 := by positivity
  have hL1 : 2 * ((cfg.r₁ : ℝ) / 4) ≤ 1 := by linarith
  have hδL : (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ) / 4 := by linarith
  have hr₁E : (cfg.r₁ : ENNReal) = ENNReal.ofReal (4 * ((cfg.r₁ : ℝ) / 4)) := by
    rw [show 4 * ((cfg.r₁ : ℝ) / 4) = (cfg.r₁ : ℝ) by ring, ENNReal.ofReal_coe_nnreal]
  have hmem : ∀ p ∈ core.segs B, par p ∈ cfg.s := fun p hp =>
    core.fam_subset B hB p hp (hpar B hB p hp).1
  have hinj : Set.InjOn par (core.segs B : Set core.σ) := by
    intro p hp q hq hpq
    have hp' : p ∈ core.segs B := Finset.mem_coe.1 hp
    have hq' : q ∈ core.segs B := Finset.mem_coe.1 hq
    by_contra hne
    have hdisj := core.fam_disjoint B hB hp hq hne
    refine Finset.disjoint_left.1 hdisj (hpar B hB p hp').1 ?_
    rw [hpq]
    exact (hpar B hB q hq').1
  rw [← densityIn_self_maximizer_eq, hr₁E]
  exact ofReal_sq_mul_densityIn_le_of_segCarrierSet cfg.s cfg.T (core.segs B) core.Y par hmem
    hinj (core.ctr B) hL hL1 hδL (fun p hp => (hpar B hB p hp).2) _

/-! ### The core of `BallData` from a given ball cover -/

section CoreOfCover

variable (cfg : VeryNotSticky.{u}) {bι : Type u}

open scoped Classical in
/-- **The segment family of a piece**: one segment per tube whose shading meets the piece
`P B`, indexed by the pair `(tube, ball)`. This is the `segs` of
`Kakeya.VeryNotSticky.ballDataCoreOfCover`, verbatim the witness of
`Kakeya.VeryNotSticky.exists_segments`. -/
noncomputable def segsOfCover (P : bι → Set (EuclideanSpace ℝ (Fin 3))) (B : bι) :
    Finset (cfg.ι × bι) :=
  (cfg.s.filter (fun i => ((cfg.T i).shade ∩ P B).Nonempty)).image (fun i => (i, B))

/-- **The segment body of a pair (tube, ball)**: the capsule
`Kakeya.VeryNotSticky.segShadedBody` of half-length `r₁/4` along the tube, centred at the
ball's centre, shaded by `Y(T) ∩ P B`. This is the `Y` of
`Kakeya.VeryNotSticky.ballDataCoreOfCover`, verbatim the witness of
`Kakeya.VeryNotSticky.exists_segments`. -/
noncomputable def segBodyOfCover (ctr : bι → EuclideanSpace ℝ (Fin 3))
    (P : bι → Set (EuclideanSpace ℝ (Fin 3))) (hPmeas : ∀ B, MeasurableSet (P B))
    (p : cfg.ι × bι) : ShadedBody (EuclideanSpace ℝ (Fin 3)) :=
  segShadedBody (cfg.T p.1) (ctr p.2) (by positivity : (0 : ℝ) ≤ (cfg.r₁ : ℝ) / 4) (P p.2)
    (hPmeas p.2)

@[simp] lemma segBodyOfCover_carrier (ctr : bι → EuclideanSpace ℝ (Fin 3))
    (P : bι → Set (EuclideanSpace ℝ (Fin 3))) (hPmeas : ∀ B, MeasurableSet (P B))
    (p : cfg.ι × bι) :
    (segBodyOfCover cfg ctr P hPmeas p).carrier =
      segCarrierSet (cfg.T p.1).toTube (ctr p.2) ((cfg.r₁ : ℝ) / 4) := rfl

@[simp] lemma segBodyOfCover_shade (ctr : bι → EuclideanSpace ℝ (Fin 3))
    (P : bι → Set (EuclideanSpace ℝ (Fin 3))) (hPmeas : ∀ B, MeasurableSet (P B))
    (p : cfg.ι × bι) :
    (segBodyOfCover cfg ctr P hPmeas p).shade =
      (cfg.T p.1).shade ∩ P p.2 ∩ segCarrierSet (cfg.T p.1).toTube (ctr p.2) ((cfg.r₁ : ℝ) / 4) :=
  rfl

open scoped Classical in
lemma mem_segsOfCover (P : bι → Set (EuclideanSpace ℝ (Fin 3))) (B : bι) (p : cfg.ι × bι) :
    p ∈ segsOfCover cfg P B ↔
      ∃ i ∈ cfg.s, ((cfg.T i).shade ∩ P B).Nonempty ∧ (i, B) = p := by
  simp only [segsOfCover, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨i, ⟨hi, hne⟩, rfl⟩
    exact ⟨i, hi, hne, rfl⟩
  · rintro ⟨i, hi, hne, rfl⟩
    exact ⟨i, ⟨hi, hne⟩, rfl⟩

open scoped Classical in
/-- **The core of `BallData` from a given `r₁`-ball cover** (blueprint `hyp:ml2setup`, items
(C2), (C3) and the compatibility clauses of (C5)).

This is the body of `Kakeya.VeryNotSticky.exists_ballDataCore` with its internal call to
`Kakeya.VeryNotSticky.exists_ballCover` replaced by a *given* cover: the eight clauses are, in
order, the eight conclusions of `exists_ballCover` (equivalently of T1's
`Kakeya.VeryNotSticky.exists_ballCover_family` on `cfg.s`, `cfg.T`, at `r₁ = cfg.r₁`, whose ninth
conjunct is not needed). The construction is transparent: `bs`, `ctr`, `P` are the given
ones, `segs B = segsOfCover cfg P B`, `Y = segBodyOfCover cfg ctr P hPmeas`, `fam p = {p.1}`,
`m = Cm = 1`, all by `rfl` — so that the dilation clause of its capsules
(`Kakeya.VeryNotSticky.segs_dilation_ballDataCoreOfCover`) and the later (C4)/(C5) producers can
see the segments' geometry. Only the `δ`-ball covers (`γ`, `cov`, `covCtr`) are chosen
non-constructively, from `Kakeya.VeryNotSticky.exists_deltaCovers`.

The field proofs are those of `Kakeya.VeryNotSticky.exists_segments` (BallConstruction.lean) and
of `exists_ballDataCore` (the weakening of the segment constants from `4` to `C₀ ≥ 4`). -/
noncomputable def ballDataCoreOfCover {C₀ : NNReal} (hC₀ : 4 ≤ C₀)
    {D : ℕ} (hD : ballCoverConstant ≤ D) (hδr : 16 * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ))
    (bs : Finset bι) (ctr : bι → EuclideanSpace ℝ (Fin 3))
    (P : bι → Set (EuclideanSpace ℝ (Fin 3)))
    (hbsne : bs.Nonempty)
    (hPball16 : ∀ B ∈ bs, P B ⊆ ball (ctr B) ((cfg.r₁ : ℝ) / 16))
    (hPball : ∀ B ∈ bs, P B ⊆ closedBall (ctr B) (cfg.r₁ : ℝ))
    (hPdisj : (bs : Set bι).PairwiseDisjoint P)
    (hPmeas : ∀ B, MeasurableSet (P B))
    (hPcov : ∀ i ∈ cfg.s, (cfg.T i).shade ⊆ ⋃ B ∈ bs, P B)
    (hoverlap : ∀ (x : EuclideanSpace ℝ (Fin 3)) (t : Finset bι), t ⊆ bs →
      (∀ B ∈ t, x ∈ ball (ctr B) (cfg.r₁ : ℝ)) → t.card ≤ ballCoverConstant)
    (hPne : ∀ B ∈ bs, (P B ∩ ⋃ i ∈ cfg.s, (cfg.T i).shade).Nonempty) :
    BallDataCore cfg where
  C₀ := C₀
  hC₀ := le_trans (by norm_num) hC₀
  D := D
  Yg := fun i ↦ (cfg.T i).shade
  Yg_subset := fun _ _ ↦ subset_rfl
  Yg_measurable := fun i _ ↦ (cfg.T i).measurableSet_shade
  Cg := 1
  hCg := le_rfl
  Yg_mass := by simp
  bι := bι
  σ := cfg.ι × bι
  bs := bs
  bs_nonempty := hbsne
  ctr := ctr
  P := P
  P_subset_ball := hPball
  P_disjoint := hPdisj
  P_measurable := fun B _ => hPmeas B
  P_cover := hPcov
  ballOverlap := fun x t hts hball => le_trans (hoverlap x t hts hball) hD
  segs := segsOfCover cfg P
  Y := segBodyOfCover cfg ctr P hPmeas
  fam := fun p => {p.1}
  segs_nonempty := by
    intro B hB
    obtain ⟨x, hxP, hxS⟩ := hPne B hB
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hxS
    exact ⟨(i, B), (mem_segsOfCover cfg P B _).2 ⟨i, hi, ⟨x, hxi, hxP⟩, rfl⟩⟩
  fam_subset := by
    intro B hB p hp
    obtain ⟨i, hi, -, rfl⟩ := (mem_segsOfCover cfg P B p).1 hp
    simpa using hi
  fam_disjoint := by
    intro B hB p hp q hq hpq
    rw [Finset.mem_coe] at hp hq
    obtain ⟨i, -, -, rfl⟩ := (mem_segsOfCover cfg P B p).1 hp
    obtain ⟨j, -, -, rfl⟩ := (mem_segsOfCover cfg P B q).1 hq
    have hij : i ≠ j := fun h => hpq (by rw [h])
    simpa using hij
  Y_piece := by
    intro B hB p hp x hx
    obtain ⟨i, -, -, rfl⟩ := (mem_segsOfCover cfg P B p).1 hp
    exact hx.1.2
  segs_thickness := by
    intro B hB p hp
    obtain ⟨i, -, -, rfl⟩ := (mem_segsOfCover cfg P B p).1 hp
    have hr₁pos : (0 : ℝ) < (cfg.r₁ : ℝ) := by exact_mod_cast NNReal.rpow_pos cfg.hδ
    have hδ0 : (0 : ℝ) ≤ (cfg.δ : ℝ) := (cfg.δ).coe_nonneg
    have hth := hasThicknesses_segCarrierSet (cfg.T i).toTube (ctr B)
      (by positivity : (0 : ℝ) ≤ (cfg.r₁ : ℝ) / 4) (by linarith [r₁_le_one cfg])
      (by linarith)
    rw [show 4 * ((cfg.r₁ : ℝ) / 4) = (cfg.r₁ : ℝ) by ring] at hth
    have hC₀R : (4 : ℝ) ≤ ((C₀ : NNReal) : ℝ) := by exact_mod_cast hC₀
    intro k
    obtain ⟨hlo, hhi⟩ := hth k
    have htk : 0 ≤ (![(cfg.r₁ : ℝ), (cfg.δ : ℝ), (cfg.δ : ℝ)]) k := by
      have hk : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
      rcases hk with rfl | rfl | rfl <;> simp
    have h4pos : (0 : ℝ) < 4 := by norm_num
    have h4' : ((4 : NNReal) : ℝ) = 4 := by norm_num
    have hinv : ((C₀ : NNReal) : ℝ)⁻¹ ≤ (((4 : NNReal) : ℝ))⁻¹ := by
      rw [h4']
      exact inv_anti₀ h4pos hC₀R
    constructor
    · exact le_trans (mul_le_mul_of_nonneg_right hinv htk) hlo
    · refine le_trans hhi (mul_le_mul_of_nonneg_right ?_ htk)
      rw [h4']
      exact hC₀R
  segs_dims := by
    intro B hB p hp q hq
    obtain ⟨i, -, -, rfl⟩ := (mem_segsOfCover cfg P B p).1 hp
    obtain ⟨j, -, -, rfl⟩ := (mem_segsOfCover cfg P B q).1 hq
    have hr₁pos : (0 : ℝ) < (cfg.r₁ : ℝ) := by exact_mod_cast NNReal.rpow_pos cfg.hδ
    have hδ0 : (0 : ℝ) ≤ (cfg.δ : ℝ) := (cfg.δ).coe_nonneg
    exact thickness_segCarrierSet_le_two_nsmul (cfg.T i).toTube (cfg.T j).toTube
      (ctr B) (ctr B) (by positivity) (by linarith [r₁_le_one cfg]) (by linarith)
  parent := by
    intro B hB i hi hne
    exact ⟨(i, B), (mem_segsOfCover cfg P B _).2 ⟨i, hi, hne, rfl⟩,
      Finset.mem_singleton_self i⟩
  into := by
    intro B hB p hp i hi
    obtain ⟨j, -, -, rfl⟩ := (mem_segsOfCover cfg P B p).1 hp
    have hij : i = j := Finset.mem_singleton.1 hi
    subst hij
    intro x hx
    have hδ0 : (0 : ℝ) ≤ (cfg.δ : ℝ) := (cfg.δ).coe_nonneg
    have hcover : 2 * ((cfg.δ : ℝ) + (cfg.r₁ : ℝ) / 16) ≤ (cfg.r₁ : ℝ) / 4 := by linarith
    exact ⟨⟨hx.1, hx.2⟩,
      tube_inter_ball_subset_segCarrierSet (cfg.T i).toTube (ctr B) (by positivity) hcover
        ⟨(cfg.T i).shade_subset hx.1, hPball16 B hB hx.2⟩⟩
  back := by
    intro B hB p hp x hx
    obtain ⟨i, -, -, rfl⟩ := (mem_segsOfCover cfg P B p).1 hp
    exact Set.mem_biUnion (Finset.mem_singleton_self i) hx.1.1
  segs_core := by
    intro B hB p hp i hi
    obtain ⟨j, -, -, rfl⟩ := (mem_segsOfCover cfg P B p).1 hp
    have hij : i = j := Finset.mem_singleton.1 hi
    subst hij
    have hδ0 : (0 : ℝ) ≤ (cfg.δ : ℝ) := (cfg.δ).coe_nonneg
    have hC₀R : (4 : ℝ) ≤ ((C₀ : NNReal) : ℝ) := by exact_mod_cast hC₀
    refine ⟨corePt (cfg.T i).toTube (segStart (cfg.T i).toTube (ctr B) ((cfg.r₁ : ℝ) / 4)), ?_⟩
    refine subset_trans
      (segCarrierSet_subset_cthickening_line (cfg.T i).toTube (ctr B) (by positivity)
        (C := 4 * (cfg.δ : ℝ)) (by linarith))
      (Metric.cthickening_mono ?_ _)
    exact mul_le_mul_of_nonneg_right hC₀R hδ0
  m := 1
  Cm := 1
  hCm := le_refl 1
  fibre := by
    intro B hB p hp x hx
    obtain ⟨i, -, -, rfl⟩ := (mem_segsOfCover cfg P B p).1 hp
    have hcard : {j ∈ ({i} : Finset cfg.ι) | x ∈ (cfg.T j).shade} = {i} := by
      refine Finset.filter_true_of_mem ?_
      intro j hj
      rw [Finset.mem_singleton] at hj
      subst hj
      exact hx.1.1
    rw [hcard]
    simp
  γ := (exists_deltaCovers cfg.hδ (segBodyOfCover cfg ctr P hPmeas)).choose
  cov := (exists_deltaCovers cfg.hδ (segBodyOfCover cfg ctr P hPmeas)).choose_spec.choose
  covCtr :=
    (exists_deltaCovers cfg.hδ (segBodyOfCover cfg ctr P hPmeas)).choose_spec.choose_spec.choose
  cov_isCover := fun _ _ p _ =>
    ⟨((exists_deltaCovers cfg.hδ
        (segBodyOfCover cfg ctr P hPmeas)).choose_spec.choose_spec.choose_spec.1 p).subset_iUnion,
      fun x => le_trans (((exists_deltaCovers cfg.hδ
        (segBodyOfCover cfg ctr P hPmeas)).choose_spec.choose_spec.choose_spec.1 p).card_filter_le
          x) hD⟩
  cov_meets := fun _ _ p _ =>
    (exists_deltaCovers cfg.hδ
      (segBodyOfCover cfg ctr P hPmeas)).choose_spec.choose_spec.choose_spec.2 p
  segs_subset_ball := by
    intro B hB p hp
    obtain ⟨i, -, hine, rfl⟩ := (mem_segsOfCover cfg P B p).1 hp
    obtain ⟨x, hx1, hx2⟩ := hine
    have hδ0 : (0 : ℝ) ≤ (cfg.δ : ℝ) := (cfg.δ).coe_nonneg
    refine segCarrierSet_subset_closedBall_ctr (cfg.T i).toTube (ctr B)
      (ρ := (cfg.r₁ : ℝ) / 16) (by positivity)
      ⟨x, (cfg.T i).shade_subset hx1, hPball16 B hB hx2⟩ ?_
    linarith
  segs_scale := by
    intro B hB p hp
    obtain ⟨i, -, -, rfl⟩ := (mem_segsOfCover cfg P B p).1 hp
    exact le_ethickness_scale_segCarrierSet (cfg.T i).toTube (ctr B) (by positivity)

variable {cfg}

section rfl_lemmas

variable {C₀ : NNReal} (hC₀ : 4 ≤ C₀) {D : ℕ} (hD : ballCoverConstant ≤ D)
  (hδr : 16 * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ))
  (bs : Finset bι) (ctr : bι → EuclideanSpace ℝ (Fin 3))
  (P : bι → Set (EuclideanSpace ℝ (Fin 3)))
  (hbsne : bs.Nonempty)
  (hPball16 : ∀ B ∈ bs, P B ⊆ ball (ctr B) ((cfg.r₁ : ℝ) / 16))
  (hPball : ∀ B ∈ bs, P B ⊆ closedBall (ctr B) (cfg.r₁ : ℝ))
  (hPdisj : (bs : Set bι).PairwiseDisjoint P)
  (hPmeas : ∀ B, MeasurableSet (P B))
  (hPcov : ∀ i ∈ cfg.s, (cfg.T i).shade ⊆ ⋃ B ∈ bs, P B)
  (hoverlap : ∀ (x : EuclideanSpace ℝ (Fin 3)) (t : Finset bι), t ⊆ bs →
    (∀ B ∈ t, x ∈ ball (ctr B) (cfg.r₁ : ℝ)) → t.card ≤ ballCoverConstant)
  (hPne : ∀ B ∈ bs, (P B ∩ ⋃ i ∈ cfg.s, (cfg.T i).shade).Nonempty)

@[simp] lemma ballDataCoreOfCover_C₀ :
    (ballDataCoreOfCover cfg hC₀ hD hδr bs ctr P hbsne hPball16 hPball hPdisj hPmeas hPcov
      hoverlap hPne).C₀ = C₀ := rfl

@[simp] lemma ballDataCoreOfCover_D :
    (ballDataCoreOfCover cfg hC₀ hD hδr bs ctr P hbsne hPball16 hPball hPdisj hPmeas hPcov
      hoverlap hPne).D = D := rfl

@[simp] lemma ballDataCoreOfCover_bs :
    (ballDataCoreOfCover cfg hC₀ hD hδr bs ctr P hbsne hPball16 hPball hPdisj hPmeas hPcov
      hoverlap hPne).bs = bs := rfl

@[simp] lemma ballDataCoreOfCover_ctr :
    (ballDataCoreOfCover cfg hC₀ hD hδr bs ctr P hbsne hPball16 hPball hPdisj hPmeas hPcov
      hoverlap hPne).ctr = ctr := rfl

@[simp] lemma ballDataCoreOfCover_P :
    (ballDataCoreOfCover cfg hC₀ hD hδr bs ctr P hbsne hPball16 hPball hPdisj hPmeas hPcov
      hoverlap hPne).P = P := rfl

@[simp] lemma ballDataCoreOfCover_segs :
    (ballDataCoreOfCover cfg hC₀ hD hδr bs ctr P hbsne hPball16 hPball hPdisj hPmeas hPcov
      hoverlap hPne).segs = segsOfCover cfg P := rfl

@[simp] lemma ballDataCoreOfCover_Y :
    (ballDataCoreOfCover cfg hC₀ hD hδr bs ctr P hbsne hPball16 hPball hPdisj hPmeas hPcov
      hoverlap hPne).Y = segBodyOfCover cfg ctr P hPmeas := rfl

@[simp] lemma ballDataCoreOfCover_fam (p : cfg.ι × bι) :
    (ballDataCoreOfCover cfg hC₀ hD hδr bs ctr P hbsne hPball16 hPball hPdisj hPmeas hPcov
      hoverlap hPne).fam p = {p.1} := rfl

@[simp] lemma ballDataCoreOfCover_m :
    (ballDataCoreOfCover cfg hC₀ hD hδr bs ctr P hbsne hPball16 hPball hPdisj hPmeas hPcov
      hoverlap hPne).m = 1 := rfl

@[simp] lemma ballDataCoreOfCover_Cm :
    (ballDataCoreOfCover cfg hC₀ hD hδr bs ctr P hbsne hPball16 hPball hPdisj hPmeas hPcov
      hoverlap hPne).Cm = 1 := rfl

/-- **The dilation clause of the capsules of `ballDataCoreOfCover`**: the field
`Kakeya.VeryNotSticky.BallData.segs_dilation` for this core at
`Cdil := Kakeya.VeryNotSticky.segsDilationConstant`, i.e. exactly the `hdil` that
`Kakeya.VeryNotSticky.BallDataCore.nonempty_ballData_of_dilation` and
`Kakeya.VeryNotSticky.BallDataCore.toBallData` take. -/
theorem segs_dilation_ballDataCoreOfCover :
    ∀ B ∈ (ballDataCoreOfCover cfg hC₀ hD hδr bs ctr P hbsne hPball16 hPball hPdisj hPmeas hPcov
        hoverlap hPne).bs,
      (cfg.r₁ : ENNReal) ^ 2 *
          maxDensity ((ballDataCoreOfCover cfg hC₀ hD hδr bs ctr P hbsne hPball16 hPball hPdisj
              hPmeas hPcov hoverlap hPne).segs B)
            (fun p ↦ ((ballDataCoreOfCover cfg hC₀ hD hδr bs ctr P hbsne hPball16 hPball hPdisj
              hPmeas hPcov hoverlap hPne).Y p).toConvexSpaceBody) ≤
        (segsDilationConstant : ENNReal) *
          maxDensity cfg.s (fun i ↦ (cfg.T i).toConvexSpaceBody) := by
  refine segs_dilation_capsules _ hδr Prod.fst fun B hB p hp => ?_
  obtain ⟨i, -, -, rfl⟩ := (mem_segsOfCover cfg P B p).1 hp
  exact ⟨Finset.mem_singleton_self i, rfl⟩

end rfl_lemmas

/-- **The core of `BallData` from a given ball cover**, in `Nonempty` form: the statement of
`Kakeya.VeryNotSticky.exists_ballDataCore` with its internal `exists_ballCover` replaced by the
given cover (the eight conclusions of `exists_ballCover`, equivalently of T1's
`Kakeya.VeryNotSticky.exists_ballCover_family` at `cfg.s`, `cfg.T`, `r₁ = cfg.r₁`). The witness is
`Kakeya.VeryNotSticky.ballDataCoreOfCover`; `exists_ballDataCore` itself is recovered by feeding
it the cover of `exists_ballCover_family`. -/
theorem exists_ballDataCore_of_cover (cfg : VeryNotSticky.{u}) {C₀ : NNReal} (hC₀ : 4 ≤ C₀)
    {D : ℕ} (hD : ballCoverConstant ≤ D) (hδr : 16 * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ))
    {bι : Type u} {bs : Finset bι} {ctr : bι → EuclideanSpace ℝ (Fin 3)}
    {P : bι → Set (EuclideanSpace ℝ (Fin 3))}
    (hbsne : bs.Nonempty)
    (hPball16 : ∀ B ∈ bs, P B ⊆ ball (ctr B) ((cfg.r₁ : ℝ) / 16))
    (hPball : ∀ B ∈ bs, P B ⊆ closedBall (ctr B) (cfg.r₁ : ℝ))
    (hPdisj : (bs : Set bι).PairwiseDisjoint P)
    (hPmeas : ∀ B, MeasurableSet (P B))
    (hPcov : ∀ i ∈ cfg.s, (cfg.T i).shade ⊆ ⋃ B ∈ bs, P B)
    (hoverlap : ∀ (x : EuclideanSpace ℝ (Fin 3)) (t : Finset bι), t ⊆ bs →
      (∀ B ∈ t, x ∈ ball (ctr B) (cfg.r₁ : ℝ)) → t.card ≤ ballCoverConstant)
    (hPne : ∀ B ∈ bs, (P B ∩ ⋃ i ∈ cfg.s, (cfg.T i).shade).Nonempty) :
    Nonempty (BallDataCore cfg) :=
  ⟨ballDataCoreOfCover cfg hC₀ hD hδr bs ctr P hbsne hPball16 hPball hPdisj hPmeas hPcov hoverlap
    hPne⟩

end CoreOfCover


end Kakeya.VeryNotSticky

/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.TangentialCase

/-!
# The Katz–Tao input of the tangential slab step, from `K_KT(β)`

The Katz--Tao estimate at the scale used by the tangential argument.

`Kakeya.VeryNotSticky.ktRho2ScaleData_of_katzTaoEstimate` produces, from `K_KT(β)`
(`Kakeya.KatzTaoEstimate`, GWZ Definition 3.4, `gwz.txt` l.261–267), the fullness threshold
`η₁ = η₁(ϱ, β) > 0` of GWZ Lemma 3.7 (`gwz.txt` l.330–336; blueprint `genKKT`,
`Kakeya.KatzTaoEstimate.multiplicity_bound_generalize`, read through Remark 3.6 =
blueprint `multBoundsDeltaVsRho`, `gwz.txt` l.294–310) such that, for every small `δ`, every
configuration at the parameters `(δ, β, ϱ)` with `bd.C₀ = C₀` and `ρ₂ ≤ δ^e` satisfies
`cfg.KTRho2ScaleData bd (4ϱ) η₁ (3ϱ)`: any family of bodies comparable (constant `2 C₀`) to
`ρ₂`-tubes in the unit ball, Katz–Tao at `δ^{-3ϱ}` and `δ^{η₁}`-full, has multiplicity at most
`δ^{-4ϱ} |𝕋|^β`. This is the analytic half of the tangential slab step, GWZ (104)
(`gwz.txt` l.2389–2392): `µ(𝕋̃) ⪅ δ^{-O(ηbias)} δ^{-ηbias(1-β)} |𝕋̃|^β`, with the tree's `ϱ` for
GWZ's `ηbias`, the `Δ_max` level `δ^{-3ϱ}` that `Kakeya.VeryNotSticky.slabKatzTao` supplies, and
the loss `4ϱ ≥ ϱ/2 + ϱ/2 + 3ϱ(1-β)`.

## Route

* Lemma 3.7 is stated for `ShadedTube` families with unit cores, while the estimate quantifies
  over `ShadedBody` families with the thickness profile `(1, ρ₂, ρ₂)` (see the docstring of
  `Kakeya.VeryNotSticky.KTRho2ScaleData` for why). A body with that profile inside `B₁` may have
  diameter `2`, so it is first shrunk by the homothety of centre `0` and ratio `1/8`
  (`ShadedBody.homothety`): multiplicity, fullness and the Katz–Tao bound are exactly invariant
  (`ShadedBody.multiplicity_homothety`, `ShadedBody.fullness_homothety`,
  `ConvexSpaceBody.IsKatzTao.homothety`), and the image lies in `B_{1/8}` with `1`-thickness
  `≤ C₀ ρ₂ / 4`.
* Each shrunk body is enclosed in the `r`-tube, `r = C₀ ρ₂`, around the unit segment centred at
  the foot of one of its points on the attained thickness line
  (`Metric.exists_subset_cthickening_thickness_finrank_eq`); the tube lies in `B₁`
  (`Kakeya.VeryNotSticky.exists_tube_of_thickness_one_le`). The shading is carried over
  unchanged, so multiplicities agree; the carriers grow by at most the factor
  `Kakeya.VeryNotSticky.ktRho2EnclosureConstant C₀ = 16 · 512 · 48 · C₀⁵` (tube volume
  `≤ 16 r²` against the inscribed-simplex bound `|W| ≥ ρ₂² / (6 (2C₀)³)` and the homothety
  factor `8³`), which is what fullness loses and `Δ_max` gains
  (`ConvexSpaceBody.IsVolumeControlledEnlargement.isKatzTao`).
* Lemma 3.7 in its Remark 3.6 form is then applied at tube scale `r` and Katz–Tao parameter
  `τ = δ ≤ r` (`δ ≤ b ≤ ρ₂ ≤ r` from `cfg.hdims`), at loss `ϱ/2`; the `∀ᶠ` of the lemma is in
  the tube scale, which is where the hypothesis `ρ₂ ≤ δ^e` enters. The enclosure constant is
  absorbed twice, into the fullness threshold (`η₁ := η/2`) and into one further `δ^{-ϱ/2}`.

The clause `6 * cfg.η ≤ η₁` of `Kakeya.VeryNotSticky.SlabMultKT.fullness_threshold` is not part
of this statement: it constrains `η` against the unspecified threshold `η₁` and is discharged by the
consumer.
-/

@[expose] public section

namespace Kakeya.VeryNotSticky

open MeasureTheory Metric Filter Topology

universe u

/-! ### Geometry: enclosing a small body in a unit tube -/

/-- **Enclosure of a small set in a unit tube.** A bounded nonempty set inside `B_{1/8}` whose
`1`-thickness is at most `r ≤ 1/8` lies in the `r`-tube (`Tube.mk'`) around a unit segment of
the attained thickness line, and that tube lies in the unit ball.

The segment is centred at the foot `a₀` of one point `k₀` of the set on the line: every other
foot is within `2r + 1/4 ≤ 1/2` of `a₀`, so the unit segment centred at `a₀` covers all feet.
This is the design step "`Tube` has a unit core, so enclosure needs a homothety first" of
, with the homothety ratio `1/8`. -/
theorem exists_tube_of_thickness_one_le {K : Set (EuclideanSpace ℝ (Fin 3))}
    (hbdd : Bornology.IsBounded K) (hne : K.Nonempty)
    (hK : K ⊆ closedBall 0 (1 / 8)) {r : NNReal} (hr : thickness ℝ K 1 ≤ r)
    (hr8 : (r : ℝ) ≤ 1 / 8) :
    ∃ x y : EuclideanSpace ℝ (Fin 3), ∃ h : dist x y = 1,
      K ⊆ (Tube.mk' r h).carrier ∧ (Tube.mk' r h).carrier ⊆ closedBall 0 1 := by
  have hfr : (1 : ℕ) ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) := by
    rw [finrank_euclideanSpace_fin]; norm_num
  obtain ⟨A, hAne, hArank, hKA⟩ := exists_subset_cthickening_thickness_finrank_eq hbdd hne hfr
  have hAclosed : IsClosed (A : Set (EuclideanSpace ℝ (Fin 3))) := A.closed_of_finiteDimensional
  have hKA' : K ⊆ ⋃ a ∈ (A : Set (EuclideanSpace ℝ (Fin 3))), closedBall a (r : ℝ) := by
    rw [← hAclosed.cthickening_eq_biUnion_closedBall r.coe_nonneg]
    exact hKA.trans (cthickening_mono hr _)
  obtain ⟨k₀, hk₀⟩ := hne
  obtain ⟨a₀, ha₀A, hk₀a₀⟩ := Set.mem_iUnion₂.mp (hKA' hk₀)
  -- a unit vector spanning the direction of `A`
  haveI : Nontrivial A.direction :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [hArank]; exact one_pos)
  obtain ⟨e', he'⟩ := exists_norm_eq A.direction zero_le_one
  set e : EuclideanSpace ℝ (Fin 3) := (e' : EuclideanSpace ℝ (Fin 3)) with he_def
  have he : ‖e‖ = 1 := he'
  have he0 : e ≠ 0 := by
    intro h0; rw [h0, norm_zero] at he; exact zero_ne_one he
  have hspan : Submodule.span ℝ {e} = A.direction := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact e'.2
    · rw [finrank_span_singleton he0, hArank]
  -- every point of `A` is `a₀ + c • e`
  have hpts : ∀ a ∈ (A : Set (EuclideanSpace ℝ (Fin 3))), ∃ c : ℝ, a = c • e + a₀ := by
    intro a ha
    have hmem : a -ᵥ a₀ ∈ A.direction := AffineSubspace.vsub_mem_direction ha ha₀A
    rw [← hspan, Submodule.mem_span_singleton] at hmem
    obtain ⟨c, hc⟩ := hmem
    refine ⟨c, ?_⟩
    rw [hc, vsub_eq_sub]; abel
  refine ⟨a₀ - (2⁻¹ : ℝ) • e, a₀ + (2⁻¹ : ℝ) • e, ?_, ?_, ?_⟩
  · rw [dist_eq_norm, show (a₀ - (2⁻¹ : ℝ) • e) - (a₀ + (2⁻¹ : ℝ) • e) = -e by module,
      norm_neg, he]
  · intro k hk
    obtain ⟨a, haA, hka⟩ := Set.mem_iUnion₂.mp (hKA' hk)
    obtain ⟨c, rfl⟩ := hpts a haA
    rw [Tube.mk'_carrier]
    refine Set.mem_iUnion₂.mpr ⟨c • e + a₀, ?_, hka⟩
    -- `|c| ≤ 1/2`
    have hc : |c| ≤ 2⁻¹ := by
      have h1 : |c| = dist (c • e + a₀) a₀ := by
        rw [dist_eq_norm, add_sub_cancel_right, norm_smul, he, mul_one, Real.norm_eq_abs]
      have hkk₀ : dist k k₀ ≤ 1 / 4 := by
        have h1 := mem_closedBall_zero_iff.mp (hK hk)
        have h2 := mem_closedBall_zero_iff.mp (hK hk₀)
        calc dist k k₀ ≤ ‖k‖ + ‖k₀‖ := dist_le_norm_add_norm k k₀
          _ ≤ 1 / 8 + 1 / 8 := add_le_add h1 h2
          _ = 1 / 4 := by norm_num
      have hka' : dist k (c • e + a₀) ≤ r := mem_closedBall.mp hka
      have hk₀a₀' : dist k₀ a₀ ≤ r := mem_closedBall.mp hk₀a₀
      calc |c| = dist (c • e + a₀) a₀ := h1
        _ ≤ dist (c • e + a₀) k + dist k k₀ + dist k₀ a₀ := dist_triangle4 _ _ _ _
        _ ≤ r + 1 / 4 + r := by
            rw [dist_comm (c • e + a₀) k]
            exact add_le_add (add_le_add hka' hkk₀) hk₀a₀'
        _ ≤ 2⁻¹ := by linarith
    rw [segment]
    refine ⟨2⁻¹ - c, 2⁻¹ + c, ?_, ?_, ?_, ?_⟩
    · linarith [(abs_le.mp hc).1, (abs_le.mp hc).2]
    · linarith [(abs_le.mp hc).1, (abs_le.mp hc).2]
    · ring
    · module
  · intro p hp
    rw [Tube.mk'_carrier] at hp
    obtain ⟨z, hz, hpz⟩ := Set.mem_iUnion₂.mp hp
    have ha₀ : ‖a₀‖ ≤ 1 / 4 := by
      have h1 := mem_closedBall_zero_iff.mp (hK hk₀)
      have h2 : dist k₀ a₀ ≤ r := mem_closedBall.mp hk₀a₀
      calc ‖a₀‖ ≤ ‖k₀‖ + dist k₀ a₀ := by
            rw [dist_eq_norm]
            calc ‖a₀‖ = ‖k₀ - (k₀ - a₀)‖ := by congr 1; abel
              _ ≤ ‖k₀‖ + ‖k₀ - a₀‖ := norm_sub_le _ _
        _ ≤ 1 / 8 + 1 / 8 := add_le_add h1 (h2.trans hr8)
        _ = 1 / 4 := by norm_num
    have hx : a₀ - (2⁻¹ : ℝ) • e ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) (3 / 4) := by
      rw [mem_closedBall_zero_iff]
      calc ‖a₀ - (2⁻¹ : ℝ) • e‖ ≤ ‖a₀‖ + ‖(2⁻¹ : ℝ) • e‖ := norm_sub_le _ _
        _ = ‖a₀‖ + 2⁻¹ := by
            rw [norm_smul, he, mul_one, Real.norm_eq_abs, abs_of_pos (by norm_num)]
        _ ≤ 3 / 4 := by linarith
    have hy : a₀ + (2⁻¹ : ℝ) • e ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) (3 / 4) := by
      rw [mem_closedBall_zero_iff]
      calc ‖a₀ + (2⁻¹ : ℝ) • e‖ ≤ ‖a₀‖ + ‖(2⁻¹ : ℝ) • e‖ := norm_add_le _ _
        _ = ‖a₀‖ + 2⁻¹ := by
            rw [norm_smul, he, mul_one, Real.norm_eq_abs, abs_of_pos (by norm_num)]
        _ ≤ 3 / 4 := by linarith
    have hz' : z ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) (3 / 4) :=
      (convex_closedBall (0 : EuclideanSpace ℝ (Fin 3)) (3 / 4)).segment_subset hx hy hz
    rw [mem_closedBall_zero_iff] at hz' ⊢
    have hpz' : dist p z ≤ r := mem_closedBall.mp hpz
    calc ‖p‖ = ‖(p - z) + z‖ := by congr 1; abel
      _ ≤ ‖p - z‖ + ‖z‖ := norm_add_le _ _
      _ = dist p z + ‖z‖ := by rw [dist_eq_norm]
      _ ≤ 1 / 8 + 3 / 4 := add_le_add (hpz'.trans hr8) hz'
      _ ≤ 1 := by norm_num

/-! ### The `1/8`-homothety -/

/-- **Thickness under a homothety**, real-valued form of `Metric.ethickness_homothety_image`:
a homothety of ratio `t ≠ 0` multiplies every affine thickness of a bounded set by `|t|`. -/
theorem thickness_homothety_image_eq {X : Set (EuclideanSpace ℝ (Fin 3))}
    (hX : Bornology.IsBounded X) (x : EuclideanSpace ℝ (Fin 3)) {t : ℝ} (ht : t ≠ 0) (n : ℕ) :
    thickness ℝ (AffineMap.homothety x t '' X) n = |t| * thickness ℝ X n := by
  have hX' : Bornology.IsBounded (AffineMap.homothety x t '' X) :=
    (Kakeya.lipschitzWith_homothety x t).isBounded_image hX
  have h := ethickness_homothety_image x ht X n
  rw [ethickness_thickness' hX' n, ethickness_thickness' hX n] at h
  have hnn : ((‖t‖₊ : NNReal) : ENNReal) = ENNReal.ofReal |t| := by
    rw [← Real.enorm_eq_ofReal_abs]; rfl
  rw [hnn, ← ENNReal.ofReal_mul (abs_nonneg t)] at h
  exact (ENNReal.ofReal_eq_ofReal_iff (thickness_nonneg _ _)
    (mul_nonneg (abs_nonneg _) (thickness_nonneg _ _))).mp h

/-- The homothety of centre `0` and ratio `t` is the scalar multiplication by `t`. -/
theorem homothety_zero_apply_eq_smul (t : ℝ) (p : EuclideanSpace ℝ (Fin 3)) :
    AffineMap.homothety (0 : EuclideanSpace ℝ (Fin 3)) t p = t • p := by
  simp [AffineMap.homothety_apply]

/-- The carrier of the homothetic image of a convex body is the image of its carrier. -/
theorem carrier_homothety_eq_image (W : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) (t : ℝ) :
    (W.homothety 0 t).carrier =
      AffineMap.homothety (0 : EuclideanSpace ℝ (Fin 3)) t '' W.carrier := rfl

/-- The `1/8`-homothety of centre `0` takes a body inside `B₁` into `B_{1/8}`. -/
theorem homothety_carrier_subset_closedBall_eighth
    (W : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) (hW : W.carrier ⊆ closedBall 0 1) :
    (W.homothety 0 (8⁻¹ : ℝ)).carrier ⊆ closedBall 0 (1 / 8) := by
  rw [carrier_homothety_eq_image]
  rintro p ⟨q, hq, rfl⟩
  rw [homothety_zero_apply_eq_smul, mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by norm_num : (0:ℝ) < 8⁻¹)]
  have := mem_closedBall_zero_iff.mp (hW hq)
  nlinarith

/-- The `1/8`-homothety divides the volume of a body in `ℝ³` by `8³ = 512`. -/
theorem volume_homothety_eighth (W : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) :
    volume (W.homothety 0 (8⁻¹ : ℝ)).carrier = ENNReal.ofReal (1 / 512) * volume W.carrier := by
  rw [ConvexSpaceBody.volume_homothety, finrank_euclideanSpace_fin]
  norm_num

/-! ### Tubes: shading and volume -/

/-- The shaded `r`-tube with core tube `Z` and the shading of a body `W` whose carrier `Z`
contains. Its shade is `W.shade` and its convex body is `Z`, both definitionally. -/
def shadedTubeOfSubset {r : NNReal} (Z : Tube r (EuclideanSpace ℝ (Fin 3)))
    (W : ShadedBody (EuclideanSpace ℝ (Fin 3))) (h : W.carrier ⊆ Z.carrier) :
    ShadedTube r (EuclideanSpace ℝ (Fin 3)) :=
  { toTube := Z, shade := W.shade, measurableSet_shade := W.measurableSet_shade,
    shade_subset := W.shade_subset.trans h }

/-- An `r`-tube in `ℝ³` with `r ≤ 1` has volume at most `16 r²` (`Tube.volume_le` at `n = 3`,
`Tube.volume_le.C 3 = 2⁴`). -/
theorem tube_volume_le_sixteen_mul_sq {r : NNReal} (hr : r ≤ 1)
    (Z : Tube r (EuclideanSpace ℝ (Fin 3))) :
    volume Z.carrier ≤ ((16 : NNReal) : ENNReal) * ((r : ENNReal) ^ (2 : ℕ)) := by
  have h := Tube.volume_le hr Z
  rw [finrank_euclideanSpace_fin] at h
  calc volume Z.carrier ≤ _ := h
    _ = ((16 : NNReal) : ENNReal) * ((r : ENNReal) ^ (2 : ℕ)) := by
        simp [Tube.volume_le.C]; norm_num

/-- **`ENNReal` form of `Kakeya.VeryNotSticky.volume_ge_of_tubeProfile` for a convex body** (the
inscribed-simplex input of `Kakeya.VeryNotSticky.slabCard`).

A convex bounded set whose affine thicknesses are comparable, with constant `C₀`, to the
`ρ`-tube profile `(1, ρ, ρ)` has volume at least `ρ² / (6 C₀³)`: the `6` is `3!`, the reciprocal
of the inscribed-simplex constant `Metric.lt_volume_convexHull.c 3` of
`Convex.prod_thickness_le_volumeReal`, and the `C₀³` is one factor of `C₀` per axis.

The real-valued statement is `Kakeya.VeryNotSticky.volume_ge_of_tubeProfile`
(`MainLemma2/TangentialCase.lean`), where the cardinality count uses it and where its single
proof lives; the `KTRho2` interface cites that lemma directly. -/
theorem ofReal_le_volume_of_tubeProfile (W : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
    {C₀ ρ : NNReal} (hC₀ : 1 ≤ C₀)
    (hprof : HasThicknesses W.carrier C₀ ![(1 : ℝ), (ρ : ℝ), (ρ : ℝ)]) :
    ENNReal.ofReal (((ρ : ℝ) ^ 2) / (6 * (C₀ : ℝ) ^ 3)) ≤ volume W.carrier := by
  have h := volume_ge_of_tubeProfile W.convex W.isCompact'.isBounded hC₀ hprof
  rw [Measure.real] at h
  exact (ENNReal.ofReal_le_iff_le_toReal W.isCompact'.measure_ne_top).mpr h

/-! ### Transport of fullness, multiplicity and the loss -/

/-- **Fullness under a volume-controlled enlargement of the carriers.** If the shaded family
`W` has the same shades as `V` on `t`, carriers at least as large and at most `K` times as
large in volume, then a fullness lower bound `x` for `V` becomes the lower bound `y` for `W`
whenever `y K ≤ x`. -/
theorem le_fullness_of_enlargement {ι : Type*} {t : Finset ι}
    {V W : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))} {K x y : ENNReal}
    (hsh : ∀ j ∈ t, (W j).shade = (V j).shade)
    (hle : ∀ j ∈ t, volume (V j).carrier ≤ volume (W j).carrier)
    (hvol : ∀ j ∈ t, volume (W j).carrier ≤ K * volume (V j).carrier)
    (h0 : ∑ j ∈ t, volume (V j).carrier ≠ 0)
    (hfull : x ≤ (ShadedBody.fullness t V : ENNReal)) (hxy : y * K ≤ x) :
    y ≤ (ShadedBody.fullness t W : ENNReal) := by
  have hVtop : ∑ j ∈ t, volume (V j).carrier ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun j _ ↦ (V j).isCompact.measure_ne_top
  have hWtop : ∑ j ∈ t, volume (W j).carrier ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun j _ ↦ (W j).isCompact.measure_ne_top
  have hW0 : ∑ j ∈ t, volume (W j).carrier ≠ 0 := fun h ↦
    h0 (le_antisymm ((Finset.sum_le_sum hle).trans h.le) bot_le)
  rw [ShadedBody.fullness_def] at hfull ⊢
  rw [ENNReal.le_div_iff_mul_le (Or.inl h0) (Or.inl hVtop)] at hfull
  rw [ENNReal.le_div_iff_mul_le (Or.inl hW0) (Or.inl hWtop)]
  rw [Finset.sum_congr rfl fun j hj ↦ congrArg volume (hsh j hj)]
  calc y * ∑ j ∈ t, volume (W j).carrier
      ≤ y * ∑ j ∈ t, K * volume (V j).carrier := by gcongr with j hj; exact hvol j hj
    _ = (y * K) * ∑ j ∈ t, volume (V j).carrier := by rw [← Finset.mul_sum, mul_assoc]
    _ ≤ x * ∑ j ∈ t, volume (V j).carrier := by gcongr
    _ ≤ ∑ j ∈ t, volume (V j).shade := hfull

/-- `ShadedBody.multiplicity` depends only on the shades of the members of `t`. -/
theorem ktRho2_multiplicity_congr_shade {ι : Type*} (t : Finset ι)
    {V W : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))}
    (h : ∀ j ∈ t, (V j).shade = (W j).shade) :
    ShadedBody.multiplicity t V = ShadedBody.multiplicity t W := by
  unfold ShadedBody.multiplicity
  rw [Finset.sum_congr rfl fun j hj ↦ congrArg volume (h j hj),
    Set.iUnion₂_congr fun j hj ↦ h j hj]

/-- **The exponent arithmetic of GWZ (104)**: Lemma 3.7 at loss `ϱ/2` with `Δ_max ≤ K δ^{-3ϱ}`
gives `δ^{-4ϱ}` once the enclosure constant `K` is absorbed into one further `δ^{-ϱ/2}`:
`δ^{-ϱ/2} · (K δ^{-3ϱ})^{1-β} ≤ δ^{-ϱ/2} · K · δ^{-3ϱ} ≤ δ^{-4ϱ}` for `0 ≤ β ≤ 1`, `1 ≤ K`,
`K ≤ δ^{-ϱ/2}` and `δ ≤ 1`. -/
theorem ktRho2_loss_arith {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {ϱ β : ℝ} (hϱ : 0 < ϱ)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) {K : ENNReal} (hK1 : 1 ≤ K)
    (hKδ : K ≤ (δ : ENNReal) ^ (-(ϱ / 2))) {Δ : ENNReal}
    (hΔ : Δ ≤ K * (δ : ENNReal) ^ (-(3 * ϱ))) (N : ENNReal) :
    (δ : ENNReal) ^ (-(ϱ / 2)) * Δ ^ (1 - β) * N ^ β ≤ (δ : ENNReal) ^ (-(4 * ϱ)) * N ^ β := by
  have hδ0' : (δ : ENNReal) ≠ 0 := by exact_mod_cast hδ0.ne'
  have hδtop : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hδ1' : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1
  have hKtop : K ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.rpow_ne_top_of_nonneg' (by exact_mod_cast hδ0) hδtop) hKδ
  have h1 : Δ ^ (1 - β) ≤ K ^ (1 - β) * ((δ : ENNReal) ^ (-(3 * ϱ))) ^ (1 - β) := by
    rw [← ENNReal.mul_rpow_of_ne_top hKtop
      (ENNReal.rpow_ne_top_of_nonneg' (by exact_mod_cast hδ0) hδtop)]
    exact ENNReal.rpow_le_rpow hΔ (by linarith)
  have h2 : K ^ (1 - β) ≤ K := by
    calc K ^ (1 - β) ≤ K ^ (1 : ℝ) := ENNReal.rpow_le_rpow_of_exponent_le hK1 (by linarith)
      _ = K := ENNReal.rpow_one K
  have h3 : ((δ : ENNReal) ^ (-(3 * ϱ))) ^ (1 - β) ≤ (δ : ENNReal) ^ (-(3 * ϱ)) := by
    rw [← ENNReal.rpow_mul]
    exact ENNReal.rpow_le_rpow_of_exponent_ge hδ1' (by nlinarith)
  calc (δ : ENNReal) ^ (-(ϱ / 2)) * Δ ^ (1 - β) * N ^ β
      ≤ (δ : ENNReal) ^ (-(ϱ / 2)) * (K * (δ : ENNReal) ^ (-(3 * ϱ))) * N ^ β := by
        gcongr
        exact h1.trans (mul_le_mul' h2 h3)
    _ ≤ (δ : ENNReal) ^ (-(ϱ / 2)) * ((δ : ENNReal) ^ (-(ϱ / 2)) * (δ : ENNReal) ^ (-(3 * ϱ)))
          * N ^ β := by gcongr
    _ = (δ : ENNReal) ^ (-(4 * ϱ)) * N ^ β := by
        rw [← ENNReal.rpow_add _ _ hδ0' hδtop, ← ENNReal.rpow_add _ _ hδ0' hδtop]
        congr 2; ring

/-- For `a > 0` and `c > 0`, eventually `δ ^ a ≤ c` as `δ → 0⁺` in `ℝ≥0`
(`ENNReal.eventually_coe_rpow_le_of_pos` read in `ℝ≥0`). -/
theorem eventually_rpow_le_of_pos_nnreal {a : ℝ} (ha : 0 < a) {c : NNReal} (hc : 0 < c) :
    ∀ᶠ δ : NNReal in 𝓝[>] 0, δ ^ a ≤ c := by
  have h := ENNReal.eventually_coe_rpow_le_of_pos ha (C := (c : ENNReal)) (by exact_mod_cast hc)
  filter_upwards [h] with δ hδ
  rw [← ENNReal.coe_rpow_of_nonneg δ ha.le] at hδ
  exact_mod_cast hδ

/-! ### The theorem -/

/-- **The enclosure constant** `16 · 512 · 48 · C₀⁵ = 393216 C₀⁵`: the volume of the enclosing
`C₀ρ₂`-tube (`≤ 16 (C₀ρ₂)²`, `Kakeya.VeryNotSticky.tube_volume_le_sixteen_mul_sq`) against the
volume of the `1/8`-homothetic image of a body with profile `(2C₀; 1, ρ₂, ρ₂)`
(`≥ 8⁻³ · ρ₂² / (6 (2C₀)³)`, `Kakeya.VeryNotSticky.ofReal_le_volume_of_tubeProfile`). -/
noncomputable def ktRho2EnclosureConstant (C₀ : NNReal) : NNReal := 393216 * C₀ ^ 5

/-- The enclosure constant is at least `1` when `1 ≤ C₀`. -/
theorem one_le_ktRho2EnclosureConstant {C₀ : NNReal} (hC₀ : 1 ≤ C₀) :
    (1 : NNReal) ≤ ktRho2EnclosureConstant C₀ := by
  unfold ktRho2EnclosureConstant
  calc (1 : NNReal) ≤ 393216 * 1 := by norm_num
    _ ≤ 393216 * C₀ ^ 5 := by gcongr; exact one_le_pow₀ hC₀

/-- **The Katz–Tao input of the tangential slab step** (blueprint `lem:ml2tangential`(b) via
`genKKT` and `multBoundsDeltaVsRho`; GWZ Lemma 3.7 with Remark 3.6 at the tangential step,
`gwz.txt` l.2387–2392, equation (104)).

From `K_KT(β)` at loss `ϱ/2` one obtains the fullness threshold `η₁ = η(ϱ, β)/2 > 0` **before**
`δ` and before the configuration — the order of quantifiers of Lemma 3.7 — such that for every
small `δ` and every configuration at `(δ, β, ϱ)` with `bd.C₀ = C₀` and `ρ₂ ≤ δ^e`, the estimate
`cfg.KTRho2ScaleData bd (4ϱ) η₁ (3ϱ)` holds: bodies comparable to `ρ₂`-tubes in `B₁`, Katz–Tao at
`δ^{-3ϱ}` and `δ^{η₁}`-full, have multiplicity `≤ δ^{-4ϱ} |𝕋|^β`.

The loss `4ϱ` is `ϱ/2` (Lemma 3.7) `+ 3ϱ(1-β)` (the factor `Δ_max^{1-β}` at `Δ_max ≤ K δ^{-3ϱ}`)
`+ ϱ/2` (absorbing the enclosure constant `K = Kakeya.VeryNotSticky.ktRho2EnclosureConstant C₀`),
see `Kakeya.VeryNotSticky.ktRho2_loss_arith`; the threshold `η₁ = η/2` absorbs `K` once more on
the fullness side. The hypothesis `ρ₂ ≤ δ^e` puts the tube scale `r = C₀ρ₂` of the enclosing
tubes below the `∀ᶠ`-threshold of Lemma 3.7; `τ = δ ≤ r` holds because `δ ≤ b ≤ ρ₂` (`cfg.hdims`). The clause
`6 * cfg.η ≤ η₁` of `Kakeya.VeryNotSticky.SlabMultKT` is the consumer's, not part of this
statement. -/
theorem ktRho2ScaleData_of_katzTaoEstimate {β ϱ e : ℝ} (hβ : 0 ≤ β) (hϱ : 0 < ϱ) (he : 0 < e)
    (C₀ : NNReal) (hC₀ : 1 ≤ C₀) (hKT : KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β) :
    ∃ η₁ > (0 : ℝ), ∀ᶠ δ in 𝓝[>] (0 : NNReal), ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg),
      cfg.δ = δ → cfg.β = β → cfg.ϱ = ϱ → bd.C₀ = C₀ → cfg.rho2 ≤ cfg.δ ^ e →
      cfg.KTRho2ScaleData bd (4 * cfg.ϱ) η₁ (3 * cfg.ϱ) := by
  -- GWZ Lemma 3.7 at loss `ϱ / 2`, in the tube scale
  obtain ⟨η, hη, hev⟩ := KatzTaoEstimate.multiplicity_bound_generalize
    (E := EuclideanSpace ℝ (Fin 3)) hβ hKT (ϱ / 2) (by positivity)
  obtain ⟨u, hu0, hsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp hev
  have hC₀pos : (0 : NNReal) < C₀ := lt_of_lt_of_le zero_lt_one hC₀
  set K : NNReal := ktRho2EnclosureConstant C₀ with hK_def
  have hK1 : (1 : NNReal) ≤ K := one_le_ktRho2EnclosureConstant hC₀
  have hKpos : (0 : NNReal) < K := lt_of_lt_of_le zero_lt_one hK1
  refine ⟨η / 2, by positivity, ?_⟩
  have hT1 := eventually_rpow_le_of_pos_nnreal he (c := u / C₀) (div_pos hu0 hC₀pos)
  have hT2 := eventually_rpow_le_of_pos_nnreal he (c := (8 * C₀)⁻¹) (by positivity)
  have hT3 := eventually_rpow_le_of_pos_nnreal (half_pos hη) (c := K⁻¹) (by positivity)
  have hT4 := eventually_rpow_le_of_pos_nnreal (half_pos hϱ) (c := K⁻¹) (by positivity)
  filter_upwards [hT1, hT2, hT3, hT4] with δ h1 h2 h3 h4
  intro cfg bd hδ hβ' hϱ' hC₀' hρe
  subst hδ hβ' hϱ' hC₀'
  intro t T hball hthick hKTt hfull
  rcases t.eq_empty_or_nonempty with rfl | htne
  · simp
  -- basic facts about the configuration: `δ ≤ b ≤ ρ₂`
  have hδ0 : 0 < cfg.δ := cfg.hδ
  have hδ1 : cfg.δ ≤ 1 := cfg.hδ1
  set ρ : NNReal := cfg.rho2 with hρ_def
  have hr₁pos : 0 < cfg.r₁ := NNReal.rpow_pos hδ0
  have hr₁le : cfg.r₁ ≤ 1 := NNReal.rpow_le_one hδ1 cfg.hexscal.le
  have hδρ : cfg.δ ≤ ρ := by
    have hb : cfg.δ ≤ cfg.b := cfg.hdims.1.trans cfg.hdims.2.1
    refine hb.trans ?_
    rw [hρ_def, VeryNotSticky.rho2, le_div_iff₀ hr₁pos]
    exact mul_le_of_le_one_right bot_le hr₁le
  have hρpos : 0 < ρ := lt_of_lt_of_le hδ0 hδρ
  -- the tube scale `r = C₀ ρ₂`
  set r : NNReal := bd.C₀ * ρ with hr_def
  have hr0 : 0 < r := mul_pos hC₀pos hρpos
  have hru : r ≤ u := by
    calc r = bd.C₀ * ρ := rfl
      _ ≤ bd.C₀ * cfg.δ ^ e := by gcongr
      _ ≤ bd.C₀ * (u / bd.C₀) := by gcongr
      _ = u := mul_div_cancel₀ u hC₀pos.ne'
  have hr8 : (r : ℝ) ≤ 1 / 8 := by
    have : r ≤ 1 / 8 := by
      calc r = bd.C₀ * ρ := rfl
        _ ≤ bd.C₀ * cfg.δ ^ e := by gcongr
        _ ≤ bd.C₀ * (8 * bd.C₀)⁻¹ := by gcongr
        _ = 1 / 8 := by
            rw [mul_inv, ← mul_assoc, mul_comm bd.C₀, mul_assoc, mul_inv_cancel₀ hC₀pos.ne',
              mul_one, one_div]
    exact_mod_cast this
  have hr1 : r ≤ 1 := by
    have : (r : ℝ) ≤ 1 := hr8.trans (by norm_num)
    exact_mod_cast this
  have hδr : cfg.δ ≤ r := by
    calc cfg.δ ≤ ρ := hδρ
      _ = 1 * ρ := (one_mul ρ).symm
      _ ≤ bd.C₀ * ρ := by gcongr
  -- Lemma 3.7 at tube radius `r` and Katz–Tao parameter `δ`
  have hgen : ∀ (s : Finset bd.ω) (T' : bd.ω → ShadedTube r (EuclideanSpace ℝ (Fin 3))),
      (∀ i, (T' i).carrier ⊆ closedBall 0 1) →
      ShadedBody.fullness s (fun i ↦ (T' i).toShadedBody) ≥ cfg.δ ^ η →
      ShadedBody.multiplicity s (fun i ↦ (T' i).toShadedBody) ≤
        (cfg.δ : ENNReal) ^ (-(cfg.ϱ / 2)) *
          (maxDensity s fun i ↦ (T' i).toConvexSpaceBody) ^ (1 - cfg.β) *
          (s.card : ENNReal) ^ cfg.β :=
    fun s T' hb hf ↦ hsub ⟨hr0, hru⟩ cfg.δ hδ0 hδr s T' hb hf
  -- the `1/8`-homothety of the family
  have h8 : (8⁻¹ : ℝ) ≠ 0 := by norm_num
  set W' : bd.ω → ShadedBody (EuclideanSpace ℝ (Fin 3)) :=
    fun j ↦ (T j).homothety (0 : EuclideanSpace ℝ (Fin 3)) h8 with hW'_def
  have hone_le_two : (1 : NNReal) ≤ 2 * bd.C₀ := by
    calc (1 : NNReal) ≤ bd.C₀ := hC₀
      _ = 1 * bd.C₀ := (one_mul _).symm
      _ ≤ 2 * bd.C₀ := by gcongr; norm_num
  -- enclosing tubes, shaded by the shrunk bodies; a default tube off `t`
  have hencl : ∀ j, ∃ Z : ShadedTube r (EuclideanSpace ℝ (Fin 3)), Z.carrier ⊆ closedBall 0 1 ∧
      (j ∈ t → (W' j).carrier ⊆ Z.carrier ∧ Z.shade = (W' j).shade ∧
        volume Z.carrier ≤ (K : ENNReal) * volume (W' j).carrier) := by
    intro j
    by_cases hj : j ∈ t
    · have hbdd : Bornology.IsBounded (W' j).carrier := (W' j).isCompact'.isBounded
      have hne : (W' j).carrier.Nonempty := (W' j).nonempty'
      have hball' : (W' j).carrier ⊆ closedBall 0 (1 / 8) :=
        homothety_carrier_subset_closedBall_eighth (T j).toConvexSpaceBody (hball j hj)
      have hth : thickness ℝ (W' j).carrier 1 ≤ r := by
        have h2C : thickness ℝ (T j).carrier 1 ≤ 2 * (bd.C₀ : ℝ) * (ρ : ℝ) := by
          simpa using (hthick j hj 1).2
        have hbddT : Bornology.IsBounded (T j).carrier := (T j).isCompact'.isBounded
        calc thickness ℝ (W' j).carrier 1
            = thickness ℝ (AffineMap.homothety (0 : EuclideanSpace ℝ (Fin 3)) (8⁻¹ : ℝ) ''
                (T j).carrier) 1 := rfl
          _ = |(8⁻¹ : ℝ)| * thickness ℝ (T j).carrier 1 :=
              thickness_homothety_image_eq hbddT 0 h8 1
          _ ≤ |(8⁻¹ : ℝ)| * (2 * (bd.C₀ : ℝ) * (ρ : ℝ)) := by gcongr
          _ ≤ (r : ℝ) := by
              rw [hr_def, NNReal.coe_mul, abs_of_pos (by norm_num : (0:ℝ) < 8⁻¹)]
              have : (0 : ℝ) ≤ (bd.C₀ : ℝ) * ρ := by positivity
              nlinarith
      obtain ⟨x, y, hxy, hsubK, htube⟩ :=
        exists_tube_of_thickness_one_le hbdd hne hball' hth hr8
      refine ⟨shadedTubeOfSubset (Tube.mk' r hxy) (W' j) hsubK, htube, fun _ ↦
        ⟨hsubK, rfl, ?_⟩⟩
      -- volume comparison: `16 r² = K · 8⁻³ · ρ₂² / (6 (2C₀)³)`
      have hvolT : ENNReal.ofReal (((ρ : ℝ) ^ 2) / (6 * ((2 * bd.C₀ : NNReal) : ℝ) ^ 3)) ≤
          volume (T j).carrier :=
        ofReal_le_volume_of_tubeProfile (T j).toConvexSpaceBody hone_le_two (hthick j hj)
      have hvolW' : volume (W' j).carrier = ENNReal.ofReal (1 / 512) * volume (T j).carrier :=
        volume_homothety_eighth (T j).toConvexSpaceBody
      calc volume (shadedTubeOfSubset (Tube.mk' r hxy) (W' j) hsubK).carrier
          = volume (Tube.mk' r hxy).carrier := rfl
        _ ≤ ((16 : NNReal) : ENNReal) * ((r : ENNReal) ^ (2 : ℕ)) :=
            tube_volume_le_sixteen_mul_sq hr1 _
        _ = (K : ENNReal) * (ENNReal.ofReal (1 / 512) *
              ENNReal.ofReal (((ρ : ℝ) ^ 2) / (6 * ((2 * bd.C₀ : NNReal) : ℝ) ^ 3))) := by
            have hreal : (16 : ℝ) * ((r : ℝ)) ^ 2 =
                (K : ℝ) * (1 / 512 * (((ρ : ℝ) ^ 2) / (6 * ((2 * bd.C₀ : NNReal) : ℝ) ^ 3))) := by
              rw [hK_def, ktRho2EnclosureConstant, hr_def]
              push_cast
              field_simp
              ring
            calc ((16 : NNReal) : ENNReal) * ((r : ENNReal) ^ (2 : ℕ))
                = ENNReal.ofReal ((16 : ℝ) * ((r : ℝ)) ^ 2) := by
                  rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow r.coe_nonneg,
                    ENNReal.ofReal_coe_nnreal]
                  congr 1
                  simp
              _ = ENNReal.ofReal ((K : ℝ) *
                    (1 / 512 * (((ρ : ℝ) ^ 2) / (6 * ((2 * bd.C₀ : NNReal) : ℝ) ^ 3)))) := by
                  rw [hreal]
              _ = (K : ENNReal) * (ENNReal.ofReal (1 / 512) *
                    ENNReal.ofReal (((ρ : ℝ) ^ 2) / (6 * ((2 * bd.C₀ : NNReal) : ℝ) ^ 3))) := by
                  rw [ENNReal.ofReal_mul K.coe_nonneg, ENNReal.ofReal_mul (by norm_num),
                    ENNReal.ofReal_coe_nnreal]
        _ ≤ (K : ENNReal) * (ENNReal.ofReal (1 / 512) * volume (T j).carrier) := by gcongr
        _ = (K : ENNReal) * volume (W' j).carrier := by rw [hvolW']
    · -- default tube with empty shade, around the origin
      have hth0 : thickness ℝ ({(0 : EuclideanSpace ℝ (Fin 3))} : Set _) 1 ≤ r :=
        thickness_le_of_subset_closedBall (x := (0 : EuclideanSpace ℝ (Fin 3))) (by simp)
          r.coe_nonneg 1
      obtain ⟨x, y, hxy, -, htube⟩ :=
        exists_tube_of_thickness_one_le (K := {(0 : EuclideanSpace ℝ (Fin 3))})
          Bornology.isBounded_singleton (Set.singleton_nonempty _) (by simp) hth0 hr8
      let Z : ShadedTube r (EuclideanSpace ℝ (Fin 3)) :=
        { toTube := Tube.mk' r hxy
          shade := ∅
          measurableSet_shade := MeasurableSet.empty
          shade_subset := Set.empty_subset _ }
      exact ⟨Z, htube, fun h ↦ absurd h hj⟩
  choose T' hT' using hencl
  have hball' : ∀ j, (T' j).carrier ⊆ closedBall 0 1 := fun j ↦ (hT' j).1
  have hsubj : ∀ j ∈ t, (W' j).carrier ⊆ (T' j).carrier := fun j hj ↦ ((hT' j).2 hj).1
  have hshj : ∀ j ∈ t, (T' j).shade = (W' j).shade := fun j hj ↦ ((hT' j).2 hj).2.1
  have hvolj : ∀ j ∈ t, volume (T' j).carrier ≤ (K : ENNReal) * volume (W' j).carrier :=
    fun j hj ↦ ((hT' j).2 hj).2.2
  -- Katz–Tao control of the tube family: `Δ_max ≤ K δ^{-3ϱ}`
  have hvce : ConvexSpaceBody.IsVolumeControlledEnlargement t (fun j ↦ (W' j).toConvexSpaceBody)
      (fun j ↦ (T' j).toConvexSpaceBody) (K : ENNReal) :=
    fun j hj ↦ ⟨hsubj j hj, hvolj j hj⟩
  have hKT' : ConvexSpaceBody.IsKatzTao t (fun j ↦ (T' j).toConvexSpaceBody)
      ((K : ENNReal) * (cfg.δ : ENNReal) ^ (-(3 * cfg.ϱ))) :=
    hvce.isKatzTao (hKTt.homothety 0 h8)
  -- fullness of the tube family: `δ^{η₁} / K ≥ δ^{η}`
  have hfullW' : ((cfg.δ ^ (η / 2) : NNReal) : ENNReal) ≤
      (ShadedBody.fullness t W' : ENNReal) := by
    rw [hW'_def, ShadedBody.fullness_homothety]
    exact_mod_cast hfull
  have h0 : ∑ j ∈ t, volume (W' j).carrier ≠ 0 := by
    intro h
    obtain ⟨j, hj⟩ := htne
    have hj0 : volume (W' j).carrier = 0 := (Finset.sum_eq_zero_iff.mp h) j hj
    have hpos : 0 < volume (W' j).carrier := by
      rw [show volume (W' j).carrier = ENNReal.ofReal (1 / 512) * volume (T j).carrier from
        volume_homothety_eighth (T j).toConvexSpaceBody]
      have hT0 : 0 < volume (T j).carrier := by
        refine lt_of_lt_of_le ?_
          (ofReal_le_volume_of_tubeProfile (T j).toConvexSpaceBody hone_le_two (hthick j hj))
        rw [ENNReal.ofReal_pos]
        have : (0 : ℝ) < ρ := hρpos
        have : (0 : ℝ) < bd.C₀ := hC₀pos
        positivity
      exact ENNReal.mul_pos (by simp) hT0.ne'
    exact hpos.ne' hj0
  have hK3 : ((cfg.δ ^ η : NNReal) : ENNReal) * (K : ENNReal) ≤
      ((cfg.δ ^ (η / 2) : NNReal) : ENNReal) := by
    have h3' : (cfg.δ ^ (η / 2)) * K ≤ 1 := by
      calc (cfg.δ ^ (η / 2)) * K ≤ K⁻¹ * K := mul_le_mul_of_nonneg_right h3 bot_le
        _ = 1 := inv_mul_cancel₀ hKpos.ne'
    have hsplit : cfg.δ ^ η = cfg.δ ^ (η / 2) * cfg.δ ^ (η / 2) := by
      rw [← NNReal.rpow_add hδ0.ne', add_halves]
    have hnn : cfg.δ ^ η * K ≤ cfg.δ ^ (η / 2) := by
      rw [hsplit, mul_assoc]
      exact mul_le_of_le_one_right bot_le h3'
    exact_mod_cast hnn
  have hfullT' : ShadedBody.fullness t (fun j ↦ (T' j).toShadedBody) ≥ cfg.δ ^ η := by
    have := le_fullness_of_enlargement (t := t) (V := W') (W := fun j ↦ (T' j).toShadedBody)
      (K := (K : ENNReal)) (fun j hj ↦ hshj j hj)
      (fun j hj ↦ measure_mono (hsubj j hj)) (fun j hj ↦ hvolj j hj) h0 hfullW' hK3
    exact_mod_cast this
  -- Lemma 3.7 for the tube family
  have hmult := hgen t T' hball' hfullT'
  -- transport back: same shades, and the homothety is exact for `μ`
  have hmult_eq : ShadedBody.multiplicity t (fun j ↦ (T' j).toShadedBody) =
      ShadedBody.multiplicity t T := by
    rw [ktRho2_multiplicity_congr_shade t (W := W') (fun j hj ↦ hshj j hj), hW'_def,
      ShadedBody.multiplicity_homothety]
  have hK4 : (K : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-(cfg.ϱ / 2)) := by
    rw [ENNReal.rpow_neg, ← ENNReal.coe_rpow_of_nonneg _ (half_pos hϱ).le,
      ← ENNReal.coe_inv (NNReal.rpow_pos hδ0).ne', ENNReal.coe_le_coe,
      le_inv_comm₀ hKpos (NNReal.rpow_pos hδ0)]
    exact h4
  rw [← hmult_eq]
  refine hmult.trans ?_
  exact ktRho2_loss_arith hδ0 hδ1 hϱ hβ cfg.hβ1 (by exact_mod_cast hK1) hK4 hKT' _

end Kakeya.VeryNotSticky

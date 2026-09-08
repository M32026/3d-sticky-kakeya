/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.RandomTranslation.RigidPullback
public import Kakeya.RandomTranslation.RigidEDGood
public import Kakeya.RandomTranslation.FrostmanCancellation

/-!
# The Frostman-good event for a tuple of random rigid motions

This is the Frostman conjunct of GWZ Lemma 3.8, event `A`. Its ED counterpart, event `B`, is
`Kakeya.exists_rigid_family_ed_good` in `RigidEDGood.lean`; the two are intersected in
`RigidRandCF.lean`.

## The calibration, with nothing hidden

Fix a convex test body `K` and write `|s|` for the cardinality of the family, `c` and `M` for the
dimensional tube-volume constants `c·δ^(n-1) ≤ |T| ≤ M·δ^(n-1)`, and `C_F` for the **canonical**
Frostman constant `ConvexSpaceBody.frostmanConstant` of the input family in `B₁`. The random
variable is `X_j(ω) = #{i ∈ s | R_j(T_i) ⊆ K}` (`Kakeya.rigidCountInAt`). Three facts calibrate it:

* **deterministic cap** — `Kakeya.rigidCountIn_le_frostman_packing` gives
  `X_j ≤ C_pack · |s| · |K|` with `C_pack := C_F · M / (c · |B₁|)`, for *every* rigid motion;
* **mean** — GWZ (108), `Kakeya.prob_rigidMove_subset_volume_le`, gives
  `P[R(T_i) ⊆ K] ≤ C₁₀₈ · |K|`, hence `𝔼[X_j] ≤ C₁₀₈ · |s| · |K|`;
* **Chernoff** — `Kakeya.rigidCountIn_chernoff_tail` then applies with the cap
  `M_K := (max (C₁₀₈ · J) C_pack + 1) · |s| · |K|`, since `J · 𝔼[X_j] < M_K` by the first factor of
  the max, and `X_j ≤ M_K` by the second.

The threshold is `S_K := L · M_K` with `L := rigidMED (edNetCalibration E) δ`, so `S_K / M_K = L`
and the per-`K` failure probability is `exp (10e - L)`. Summing over the test family
`Kakeya.exists_netF_test_family`, whose cardinality is at most
`netGeomConstantC E · δ^(-netGeomConstantMRaw E)`, the union bound is exactly the arithmetic already
proved as `Kakeya.net_union_bound_lt` (taken with `M = 1`), giving failure probability
`< 1/10 < 1/4`.

## Why the Frostman constant cancels

`J = ⌈C_F⌉₊ ≥ C_F` forces `C_pack ≤ J · M / (c · |B₁|)` and `C₁₀₈ · J ≤ J · C₁₀₈`, so

`max (C₁₀₈ · J) C_pack + 1 ≤ J · (C₁₀₈ + M / (c · |B₁|) + 1)`,

i.e. the whole cap is `J` times a purely dimensional constant. The density requirement that the
threshold must meet (`Kakeya.isFrostmanIn_rigidProduct_of_count_le`) is *also* proportional to `J`,
because the ambient density `Δ(𝕋', B₂)` counts all `J · |s|` copies. The two factors of `J` cancel
and the smallness condition on `δ` becomes `L · (dimensional constant) ≤ δ^(-η)`, which is free of
`C_F` and of the family. Since `L = O(log (1/δ))`, `Kakeya.eventually_le_rpow_neg_of_le_polylog`
closes it.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology

/-! ## Rigid motions act on shaded tubes -/

namespace ShadedTube

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {δ : NNReal}

/-- The image of a set under a rigid motion has the same Lebesgue measure. -/
theorem volume_rigidMap_image (u : unitary (E →L[ℝ] E)) (v : E) (A : Set E) :
    volume (Kakeya.rigidMap u v '' A) = volume A := by
  let L : E ≃ₗᵢ[ℝ] E := Unitary.linearIsometryEquiv u
  let g : E → E := fun y : E => (L.symm : E → E) (y - v)
  have h1 : Function.LeftInverse g (Kakeya.rigidMap u v) := by
    intro x
    dsimp [g]
    rw [add_sub_cancel_right]
    rw [← Unitary.coe_linearIsometryEquiv_apply u]
    apply LinearEquiv.symm_apply_apply
  have h2 : Function.RightInverse g (Kakeya.rigidMap u v) := by
    intro y
    dsimp [g]
    change (L : E → E) (L.symm (y - v)) + v = y
    simp
  have : Kakeya.rigidMap u v '' A = g ⁻¹' A :=
    congrFun (Set.image_eq_preimage_of_inverse h1 h2) A
  rw [this]
  have hmeas_f : Measurable (Kakeya.rigidMap u v) :=
    (Kakeya.isometry_rigidMap u v).continuous.measurable
  have hmeas_g : Measurable g := by
    dsimp [g]
    exact ((L.symm : E →L[ℝ] E).continuous.comp
      (Continuous.sub continuous_id continuous_const)).measurable
  let e : E ≃ᵐ E :=
    { toEquiv := { toFun := Kakeya.rigidMap u v, invFun := g, left_inv := h1, right_inv := h2 }
      measurable_toFun := hmeas_f
      measurable_invFun := hmeas_g }
  have he : MeasurePreserving (e : E → E) volume volume := by
    change MeasurePreserving (Kakeya.rigidMap u v) volume volume
    exact Kakeya.measurePreserving_rigidMap u v
  have h_symm : MeasurePreserving (e.symm : E → E) volume volume :=
    MeasurePreserving.symm e he
  change volume ((e.symm : E → E) ⁻¹' A) = volume A
  exact MeasurePreserving.measure_preimage_equiv h_symm A

/-- **A rigid motion carries a shaded `δ`-tube to a shaded `δ`-tube**, moving the shade along with
the carrier. -/
def rigidMove (S : ShadedTube δ E) (u : unitary (E →L[ℝ] E)) (v : E) : ShadedTube δ E where
  __ := S.toTube.rigidMove u v
  shade := Kakeya.rigidMap u v '' S.shade
  measurableSet_shade := by
    let L : E ≃ₗᵢ[ℝ] E := Unitary.linearIsometryEquiv u
    let g : E → E := fun y : E => (L.symm : E → E) (y - v)
    have h1 : Function.LeftInverse g (Kakeya.rigidMap u v) := by
      intro x
      dsimp [g]
      rw [add_sub_cancel_right]
      rw [← Unitary.coe_linearIsometryEquiv_apply u]
      apply LinearEquiv.symm_apply_apply
    have h2 : Function.RightInverse g (Kakeya.rigidMap u v) := by
      intro y
      dsimp [g]
      change (L : E → E) (L.symm (y - v)) + v = y
      simp
    have this : Kakeya.rigidMap u v '' S.shade = g ⁻¹' S.shade :=
      congrFun (Set.image_eq_preimage_of_inverse h1 h2) S.shade
    change MeasurableSet (Kakeya.rigidMap u v '' S.shade)
    rw [this]
    have hmeas_g : Measurable g := by
      dsimp [g]
      exact ((L.symm : E →L[ℝ] E).continuous.comp
        (Continuous.sub continuous_id continuous_const)).measurable
    exact measurableSet_preimage hmeas_g S.measurableSet_shade
  shade_subset := by
    calc
      Kakeya.rigidMap u v '' S.shade ⊆ Kakeya.rigidMap u v '' S.carrier :=
        Set.image_mono S.shade_subset
      _ = (S.toTube.rigidMove u v).carrier := (Tube.rigidMove_carrier (S.toTube) u v).symm

@[simp]
theorem rigidMove_toTube (S : ShadedTube δ E) (u : unitary (E →L[ℝ] E)) (v : E) :
    (S.rigidMove u v).toTube = S.toTube.rigidMove u v := rfl

@[simp]
theorem rigidMove_shade (S : ShadedTube δ E) (u : unitary (E →L[ℝ] E)) (v : E) :
    (S.rigidMove u v).shade = Kakeya.rigidMap u v '' S.shade := rfl

theorem rigidMove_carrier (S : ShadedTube δ E) (u : unitary (E →L[ℝ] E)) (v : E) :
    (S.rigidMove u v).carrier = Kakeya.rigidMap u v '' S.carrier := by
  simpa using Tube.rigidMove_carrier (S.toTube) u v

@[simp]
theorem volume_rigidMove_carrier (S : ShadedTube δ E) (u : unitary (E →L[ℝ] E)) (v : E) :
    volume (S.rigidMove u v).carrier = volume S.carrier := by
  rw [rigidMove_carrier]
  exact volume_rigidMap_image u v S.carrier

@[simp]
theorem volume_rigidMove_shade (S : ShadedTube δ E) (u : unitary (E →L[ℝ] E)) (v : E) :
    volume (S.rigidMove u v).shade = volume S.shade := by
  rw [rigidMove_shade]
  exact volume_rigidMap_image u v S.shade

theorem rigidMove_toConvexSpaceBody (S : ShadedTube δ E) (u : unitary (E →L[ℝ] E)) (v : E) :
    (S.rigidMove u v).toConvexSpaceBody
      = S.toConvexSpaceBody.mapAffine (Kakeya.rigidAffineEquiv u v) := by
  apply ConvexSpaceBody.ext
  change (S.rigidMove u v).carrier =
      (S.toConvexSpaceBody.mapAffine (Kakeya.rigidAffineEquiv u v)).carrier
  rw [rigidMove_carrier, ConvexSpaceBody.mapAffine_carrier]
  change Kakeya.rigidMap u v '' S.carrier = (Kakeya.rigidAffineEquiv u v : E → E) '' S.carrier
  rw [← Kakeya.rigidAffineEquiv_coe]

theorem rigidMove_le_iff (S : ShadedTube δ E) (K : ConvexSpaceBody E)
    (u : unitary (E →L[ℝ] E)) (v : E) :
    (S.rigidMove u v).toConvexSpaceBody ≤ K
      ↔ S.toConvexSpaceBody ≤ K.mapAffine (Kakeya.rigidAffineEquiv u v).symm := by
  rw [rigidMove_toConvexSpaceBody]
  constructor
  · intro h
    exact (ConvexSpaceBody.mapAffine_le_mapAffine_iff (f := Kakeya.rigidAffineEquiv u v)).mp
      (by simpa [ConvexSpaceBody.symm_mapAffine_mapAffine] using h)
  · intro h
    simpa [ConvexSpaceBody.symm_mapAffine_mapAffine] using
      (ConvexSpaceBody.mapAffine_le_mapAffine_iff (f := Kakeya.rigidAffineEquiv u v)).mpr h

end

end ShadedTube

namespace Kakeya

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {δ : NNReal}

/-- **The `J`-fold randomised family of GWZ Lemma 3.8**: copy `j` of tube `i` is the image of `T i`
under the rigid motion `ω j`. -/
def rigidProduct {ι : Type*} (T : ι → ShadedTube δ E) (J : ℕ)
    (ω : Fin J → unitary (E →L[ℝ] E) × E) : ι × Fin J → ShadedTube δ E :=
  fun p => (T p.1).rigidMove (ω p.2).1 (ω p.2).2

@[simp]
theorem rigidProduct_apply {ι : Type*} (T : ι → ShadedTube δ E) (J : ℕ)
    (ω : Fin J → unitary (E →L[ℝ] E) × E) (p : ι × Fin J) :
    rigidProduct T J ω p = (T p.1).rigidMove (ω p.2).1 (ω p.2).2 := rfl

/-- Every copy of a tube in `B₁` moved by a rigid motion with translation part in `B₁` lies in `B₂`.
This is the **corrected** GWZ geometry: the paper writes `B₁`, but a unit translation of a tube in
`B₁` only lands in `B₂`. -/
theorem rigidProduct_carrier_subset_closedBall_two {ι : Type*} (s : Finset ι)
    (T : ι → ShadedTube δ E) (hT : ∀ i ∈ s, (T i).carrier ⊆ closedBall (0 : E) 1)
    (J : ℕ) (ω : Fin J → unitary (E →L[ℝ] E) × E) (hω : ∀ j, (ω j).2 ∈ closedBall (0 : E) 1)
    (p : ι × Fin J) (hp : p.1 ∈ s) :
    (rigidProduct T J ω p).carrier ⊆ closedBall (0 : E) 2 := by
  rw [rigidProduct_apply]
  rw [ShadedTube.rigidMove_carrier]
  calc
    Kakeya.rigidMap (ω p.2).1 (ω p.2).2 '' (T p.1).carrier
        ⊆ Kakeya.rigidMap (ω p.2).1 (ω p.2).2 '' closedBall (0 : E) 1 := by
          exact Set.image_mono (hT p.1 hp)
    _ = closedBall (Kakeya.rigidMap (ω p.2).1 (ω p.2).2 (0 : E)) (1 : ℝ) :=
          Kakeya.rigidMap_image_closedBall (ω p.2).1 (ω p.2).2 (0 : E) (1 : ℝ)
    _ = closedBall ((ω p.2).2 : E) (1 : ℝ) := by
          simp [Kakeya.rigidMap_apply]
    _ ⊆ closedBall (0 : E) (2 : ℝ) := by
          intro x hx
          rw [Metric.mem_closedBall] at hx ⊢
          have hv : dist (ω p.2).2 (0 : E) ≤ (1 : ℝ) := by
            simpa [Metric.mem_closedBall] using hω p.2
          calc
            dist x (0 : E) ≤ dist x (ω p.2).2 + dist (ω p.2).2 (0 : E) :=
              dist_triangle x (ω p.2).2 (0 : E)
            _ ≤ (1 : ℝ) + (1 : ℝ) := by
              exact add_le_add hx hv
            _ = (2 : ℝ) := by norm_num

/-- **Unrestricted `B₂` containment for the randomised family.**

`Kakeya.rigidProduct_carrier_subset_closedBall_two` is stated for indices `p` with `p.1 ∈ s`. When
*every* tube of the family lies in `B₁` -- not merely those indexed by `s` -- the containment holds
for all `p`, which is the form `FrostmanEstimate.ball2_version_edUpToMult` consumes. -/
theorem rigidProduct_carrier_subset_closedBall_two_all [Nontrivial E] {δ : NNReal}
    {ι : Type*} (T : ι → ShadedTube δ E) (J : ℕ) (ω : Fin J → unitary (E →L[ℝ] E) × E)
    (hB : ∀ i, (T i).carrier ⊆ Metric.closedBall (0 : E) 1)
    (hω : ∀ j, (ω j).2 ∈ Metric.closedBall (0 : E) 1) (p : ι × Fin J) :
    (rigidProduct T J ω p).carrier ⊆ Metric.closedBall (0 : E) 2 := by
  rw [rigidProduct_apply]
  rw [ShadedTube.rigidMove_carrier]
  calc
    Kakeya.rigidMap (ω p.2).1 (ω p.2).2 '' (T p.1).carrier
        ⊆ Kakeya.rigidMap (ω p.2).1 (ω p.2).2 '' Metric.closedBall (0 : E) 1 := by
          exact Set.image_mono (hB p.1)
    _ = Metric.closedBall (Kakeya.rigidMap (ω p.2).1 (ω p.2).2 (0 : E)) (1 : ℝ) :=
          Kakeya.rigidMap_image_closedBall (ω p.2).1 (ω p.2).2 (0 : E) (1 : ℝ)
    _ = Metric.closedBall ((ω p.2).2 : E) (1 : ℝ) := by
          simp [Kakeya.rigidMap_apply]
    _ ⊆ Metric.closedBall (0 : E) (2 : ℝ) := by
          intro x hx
          rw [Metric.mem_closedBall] at hx ⊢
          have hv : dist (ω p.2).2 (0 : E) ≤ (1 : ℝ) := by
            simpa [Metric.mem_closedBall] using hω p.2
          calc
            dist x (0 : E) ≤ dist x (ω p.2).2 + dist (ω p.2).2 (0 : E) :=
              dist_triangle x (ω p.2).2 (0 : E)
            _ ≤ (1 : ℝ) + (1 : ℝ) := by
              exact add_le_add hx hv
            _ = (2 : ℝ) := by norm_num

/-! ## From a per-test-body count bound to the Frostman property -/

/-- The fibre of the randomised product family over copy `j` is contained in `K` exactly at the
indices counted by `Kakeya.rigidCountIn`. -/
theorem filter_rigidProduct_fibre_eq {ι : Type*} (s : Finset ι) (T : ι → ShadedTube δ E)
    (K : ConvexSpaceBody E) (J : ℕ) (ω : Fin J → unitary (E →L[ℝ] E) × E) (j : Fin J) :
    (@Finset.filter ι (fun i => (rigidProduct T J ω (i, j)).toConvexSpaceBody ≤ K)
        (Classical.decPred _) s).card
      = rigidCountIn s (fun i => (T i).toTube) K (ω j) := by
  classical
  rfl

/-- **Numerator bound.** The copies contained in `K` contribute at most
`(total count) · (M_vol · δ^(n-1))` to the density numerator. -/
theorem sum_volume_rigidProduct_filter_le (hδ1 : δ ≤ 1)
    {ι : Type*} (s : Finset ι) (T : ι → ShadedTube δ E) (K : ConvexSpaceBody E)
    (J : ℕ) (ω : Fin J → unitary (E →L[ℝ] E) × E) :
    (∑ p ∈ (@Finset.filter (ι × Fin J)
        (fun p => (rigidProduct T J ω p).toConvexSpaceBody ≤ K) (Classical.decPred _)
        (s ×ˢ (Finset.univ : Finset (Fin J)))),
        volume (rigidProduct T J ω p).carrier)
      ≤ (∑ j : Fin J, ((rigidCountIn s (fun i => (T i).toTube) K (ω j) : ℕ) : ENNReal))
          * ((Tube.volume_le.C (Module.finrank ℝ E) : ENNReal)
              * (δ : ENNReal) ^ (Module.finrank ℝ E - 1)) := by
  classical
  let n : ℕ := Module.finrank ℝ E
  let Cub : ENNReal := (Tube.volume_le.C n : ENNReal)
  let Vol : ENNReal := (δ : ENNReal) ^ (n - 1)
  let F : Finset (ι × Fin J) :=
    (s ×ˢ (Finset.univ : Finset (Fin J))).filter
      (fun p : ι × Fin J => (rigidProduct T J ω p).toConvexSpaceBody ≤ K)
  have hvol_le : ∀ p : ι × Fin J, p ∈ F →
      volume (rigidProduct T J ω p).carrier ≤ Cub * Vol := by
    intro p hp
    have hne : (T p.1).toTube.x ≠ (T p.1).toTube.y := by
      intro hxy
      have hd := (T p.1).toTube.dist_eq_one
      rw [hxy, dist_self] at hd
      norm_num at hd
    haveI : Nontrivial E := ⟨⟨(T p.1).toTube.x, (T p.1).toTube.y, hne⟩⟩
    rw [rigidProduct_apply, ShadedTube.volume_rigidMove_carrier]
    simpa [Cub, Vol] using Tube.volume_le hδ1 (T p.1).toTube
  have hsum_le : (∑ p ∈ F, volume (rigidProduct T J ω p).carrier) ≤
      (F.card : ENNReal) * (Cub * Vol) := by
    have hs := Finset.sum_le_card_nsmul F
      (fun p => volume (rigidProduct T J ω p).carrier) (Cub * Vol) hvol_le
    simpa [nsmul_eq_mul] using hs
  have hcard : F.card = ∑ j : Fin J, rigidCountIn s (fun i => (T i).toTube) K (ω j) := by
    calc
      F.card = ((s ×ˢ (Finset.univ : Finset (Fin J))).filter
          (fun p : ι × Fin J => (rigidProduct T J ω p).toConvexSpaceBody ≤ K)).card := by
            rfl
      _ = ∑ p ∈ (s ×ˢ (Finset.univ : Finset (Fin J))),
          (if (rigidProduct T J ω p).toConvexSpaceBody ≤ K then (1 : ℕ) else 0) := by
            rw [Finset.card_filter]
      _ = ∑ j : Fin J, ∑ i ∈ s,
          (if (rigidProduct T J ω (i, j)).toConvexSpaceBody ≤ K then (1 : ℕ) else 0) := by
            exact Finset.sum_product_right' (s := s) (t := (Finset.univ : Finset (Fin J)))
              (f := fun i j =>
                if (rigidProduct T J ω (i, j)).toConvexSpaceBody ≤ K then (1 : ℕ) else 0)
      _ = ∑ j : Fin J,
          (s.filter (fun i => (rigidProduct T J ω (i, j)).toConvexSpaceBody ≤ K)).card := by
            exact Finset.sum_congr rfl (fun j hj =>
              Finset.sum_boole (fun i : ι => (rigidProduct T J ω (i, j)).toConvexSpaceBody ≤ K) s)
      _ = ∑ j : Fin J, rigidCountIn s (fun i => (T i).toTube) K (ω j) := by
            exact Finset.sum_congr rfl (fun j hj =>
              filter_rigidProduct_fibre_eq s T K J ω j)
  have hcardE : (F.card : ENNReal) =
      ∑ j : Fin J, ((rigidCountIn s (fun i => (T i).toTube) K (ω j) : ℕ) : ENNReal) := by
    rw [hcard, Nat.cast_sum]
  calc
    (∑ p ∈ F, volume (rigidProduct T J ω p).carrier) ≤
        (F.card : ENNReal) * (Cub * Vol) := hsum_le
    _ = (∑ j : Fin J, ((rigidCountIn s (fun i => (T i).toTube) K (ω j) : ℕ) : ENNReal))
          * (Cub * Vol) := by
          rw [hcardE]

/-- **Denominator bound.** All `J · |s|` copies contribute at least `c_vol · δ^(n-1)` each. -/
theorem sum_volume_rigidProduct_ge {ι : Type*} (s : Finset ι) (T : ι → ShadedTube δ E)
    (J : ℕ) (ω : Fin J → unitary (E →L[ℝ] E) × E) :
    ((J : ENNReal) * (s.card : ENNReal) *
        ((Tube.le_volume.c (Module.finrank ℝ E) : ENNReal)
          * (δ : ENNReal) ^ (Module.finrank ℝ E - 1)))
      ≤ ∑ p ∈ (s ×ˢ (Finset.univ : Finset (Fin J))),
          volume (rigidProduct T J ω p).carrier := by
  classical
  have hvol : ∀ p ∈ (s ×ˢ (Finset.univ : Finset (Fin J))),
      (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal) *
          (δ : ENNReal) ^ (Module.finrank ℝ E - 1) ≤
        volume (rigidProduct T J ω p).carrier := by
    intro p hp
    have hne : (T p.1).toTube.x ≠ (T p.1).toTube.y := by
      intro hxy
      have hd := (T p.1).toTube.dist_eq_one
      rw [hxy, dist_self] at hd
      norm_num at hd
    haveI : Nontrivial E := ⟨⟨(T p.1).toTube.x, (T p.1).toTube.y, hne⟩⟩
    rw [rigidProduct_apply, ShadedTube.volume_rigidMove_carrier]
    exact Tube.le_volume (T p.1).toTube
  have hcard : (s ×ˢ (Finset.univ : Finset (Fin J))).card = s.card * J := by
    rw [Finset.card_product]
    simp [Fintype.card_fin]
  have hprod : ((s.card * J : ℕ) : ENNReal) = (J : ENNReal) * (s.card : ENNReal) := by
    norm_cast
    exact Nat.mul_comm s.card J
  calc
    (J : ENNReal) * (s.card : ENNReal) *
          ((Tube.le_volume.c (Module.finrank ℝ E) : ENNReal) *
            (δ : ENNReal) ^ (Module.finrank ℝ E - 1))
        = ((s ×ˢ (Finset.univ : Finset (Fin J))).card : ENNReal) *
            ((Tube.le_volume.c (Module.finrank ℝ E) : ENNReal) *
              (δ : ENNReal) ^ (Module.finrank ℝ E - 1)) := by
          rw [hcard, ← hprod]
    _ ≤ ∑ p ∈ (s ×ˢ (Finset.univ : Finset (Fin J))),
        volume (rigidProduct T J ω p).carrier := by
      simpa [nsmul_eq_mul] using
        (Finset.card_nsmul_le_sum (s ×ˢ (Finset.univ : Finset (Fin J)))
          (fun p => volume (rigidProduct T J ω p).carrier)
          ((Tube.le_volume.c (Module.finrank ℝ E) : ENNReal) *
            (δ : ENNReal) ^ (Module.finrank ℝ E - 1))
          hvol)

/-- **The count-to-density conversion.**

If, for every member `K` of a test family with the density-covering property, the total number of
randomised copies contained in `K` is at most `A · |s| · |K|`, and the purely numerical condition
`hA` holds, then the randomised family is `δ^(-η)`-convex-Frostman in `B₂`.

`hA` is where the two factors of `J` cancel: the left-hand side comes from the count threshold and
the right-hand side from the ambient density `Δ(𝕋', B₂)`, which counts all `J · |s|` copies. -/
theorem isFrostmanIn_rigidProduct_of_count_le [Nontrivial E]
    (hδ_pos : 0 < δ) (hδ1 : δ ≤ 1)
    {ι : Type*} (s : Finset ι) (T : ι → ShadedTube δ E)
    (hT_ball : ∀ i ∈ s, (T i).carrier ⊆ closedBall (0 : E) 1)
    (hs_card : 0 < s.card)
    (J : ℕ) (hJ : 0 < J) (ω : Fin J → unitary (E →L[ℝ] E) × E)
    (hω : ∀ j, (ω j).2 ∈ closedBall (0 : E) 1)
    (NetF : Finset (ConvexSpaceBody E)) (C_cover : ℝ) (hC_cover : 0 < C_cover)
    (hcover : ∀ K' : ConvexSpaceBody E,
      K' ≤ ConvexSpaceBody.cthickening 1 (ConvexSpaceBody.closedUnitBall (E := E)) →
      ∃ K ∈ NetF,
        densityIn (s ×ˢ (Finset.univ : Finset (Fin J)))
            (fun p => (rigidProduct T J ω p).toConvexSpaceBody) K'
          ≤ ENNReal.ofReal C_cover *
            densityIn (s ×ˢ (Finset.univ : Finset (Fin J)))
              (fun p => (rigidProduct T J ω p).toConvexSpaceBody) K)
    {A η : ℝ} (hA_nn : 0 ≤ A)
    (hcount : ∀ K ∈ NetF,
      (∑ j : Fin J, ((rigidCountIn s (fun i => (T i).toTube) K (ω j) : ℕ) : ℝ))
        ≤ A * (s.card : ℝ) * volume.real K.carrier)
    (hA : A * (Tube.volume_le.C (Module.finrank ℝ E) : ℝ) * C_cover *
            volume.real
              (ConvexSpaceBody.cthickening 1 (ConvexSpaceBody.closedUnitBall (E := E))).carrier
          ≤ (δ : ℝ) ^ (-η) * (J : ℝ) *
              (Tube.le_volume.c (Module.finrank ℝ E) : ℝ)) :
    ConvexSpaceBody.IsFrostmanIn (s ×ˢ (Finset.univ : Finset (Fin J)))
      (fun p => (rigidProduct T J ω p).toConvexSpaceBody)
      (ConvexSpaceBody.cthickening 1 (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E))
      (ENNReal.ofReal ((δ : ℝ) ^ (-η))) := by
  classical
  intro K₀ hK₀
  set B2 : ConvexSpaceBody E :=
    ConvexSpaceBody.cthickening 1 (ConvexSpaceBody.closedUnitBall (E := E))
  set s' : Finset (ι × Fin J) := s ×ˢ (Finset.univ : Finset (Fin J))
  set W' : ι × Fin J → ConvexSpaceBody E :=
    fun p => (rigidProduct T J ω p).toConvexSpaceBody
  set n : ℕ := Module.finrank ℝ E
  set CC : ENNReal := ENNReal.ofReal ((δ : ℝ) ^ (-η))
  set δp : ENNReal := (δ : ENNReal) ^ (n - 1)
  set Dcap : ENNReal := (Tube.volume_le.C n : ENNReal) * δp
  have hB2_red : B2.carrier = Metric.closedBall (0 : E) 2 := by
    dsimp [B2]
    rw [cthickening_closedUnitBall_carrier (E := E) 1 (by norm_num : (0 : ℝ) ≤ 1)]
    norm_num
  have hC_cover_nn : 0 ≤ C_cover := le_of_lt hC_cover
  have hA_mul_nn : 0 ≤ A * (s.card : ℝ) := mul_nonneg hA_nn (Nat.cast_nonneg _)
  have hs_card_pos : 0 < (s.card : ℝ) := by exact_mod_cast hs_card
  have hs_card_nn : 0 ≤ (s.card : ℝ) := le_of_lt hs_card_pos
  have hvB2r_pos : 0 < volume.real B2.carrier := by
    rw [hB2_red]
    exact volume_real_closedBall_pos (E := E) (by norm_num)
  have hvB2r_nn : 0 ≤ volume.real B2.carrier := le_of_lt hvB2r_pos
  have hvolB2_ne0 : volume B2.carrier ≠ 0 := by
    rw [hB2_red]
    exact (Metric.measure_closedBall_pos volume (0 : E) (by norm_num)).ne'
  have hvolB2_neTop : volume B2.carrier ≠ ⊤ := B2.isCompact.measure_ne_top
  have hvolB2_ofReal : ENNReal.ofReal (volume.real B2.carrier) = volume B2.carrier := by
    rw [MeasureTheory.Measure.real_def]
    exact ENNReal.ofReal_toReal hvolB2_neTop
  obtain ⟨K, hK_netF, hcoverK0⟩ := hcover K₀ hK₀
  by_cases hKvol0 : volume K.carrier = 0
  · have hdensK : densityIn s' W' K = 0 := densityIn_eq_zero_of_volume_eq_zero hKvol0
    have hle0 : densityIn s' W' K₀ ≤ 0 := hcoverK0.trans (by simp [hdensK])
    exact hle0.trans (bot_le : (0 : ENNReal) ≤ CC * densityIn s' W' B2)
  · have hKvol_ne0 : volume K.carrier ≠ 0 := hKvol0
    have hKvol_neTop : volume K.carrier ≠ ⊤ := K.isCompact.measure_ne_top
    have hvolK_ofReal : ENNReal.ofReal (volume.real K.carrier) = volume K.carrier := by
      rw [MeasureTheory.Measure.real_def]
      exact ENNReal.ofReal_toReal hKvol_neTop
    have hδ_ne0 : (δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr (ne_of_gt hδ_pos)
    have hδp_ne0 : δp ≠ 0 := by
      dsimp [δp]
      exact pow_ne_zero (n - 1) hδ_ne0
    have hδp_neTop : δp ≠ ⊤ := by
      dsimp [δp]
      exact ENNReal.pow_ne_top ENNReal.coe_ne_top
    have hcountENN :
        (∑ j : Fin J, ((rigidCountIn s (fun i => (T i).toTube) K (ω j) : ℕ) : ENNReal)) ≤
          ENNReal.ofReal (A * (s.card : ℝ) * volume.real K.carrier) := by
      have h0 := ENNReal.ofReal_le_ofReal (hcount K hK_netF)
      convert h0 using 1
      rw [ENNReal.ofReal_sum_of_nonneg (s := Finset.univ) (fun j _ => Nat.cast_nonneg _)]
      simp [ENNReal.ofReal_natCast]
    have hsum_bound :
        (∑ p ∈ s' with W' p ≤ K, volume (W' p).carrier) ≤
          (ENNReal.ofReal (A * (s.card : ℝ)) * Dcap) * volume K.carrier := by
      calc
        (∑ p ∈ s' with W' p ≤ K, volume (W' p).carrier)
            ≤ (∑ j : Fin J,
                ((rigidCountIn s (fun i => (T i).toTube) K (ω j) : ℕ) : ENNReal)) *
                Dcap := by
              simpa [s', W', Dcap, δp, n] using
                sum_volume_rigidProduct_filter_le hδ1 s T K J ω
        _ ≤ ENNReal.ofReal (A * (s.card : ℝ) * volume.real K.carrier) * Dcap := by
              exact mul_le_mul_of_nonneg_right hcountENN bot_le
        _ = (ENNReal.ofReal (A * (s.card : ℝ)) * volume K.carrier) * Dcap := by
              rw [ENNReal.ofReal_mul hA_mul_nn, hvolK_ofReal]
        _ = (ENNReal.ofReal (A * (s.card : ℝ)) * Dcap) * volume K.carrier := by ring
    have hUK : densityIn s' W' K ≤ ENNReal.ofReal (A * (s.card : ℝ)) * Dcap := by
      exact (densityIn_le_iff s' W' K (ENNReal.ofReal (A * (s.card : ℝ)) * Dcap)).2
        hsum_bound
    have hW'_le_B2 : ∀ p ∈ s', W' p ≤ B2 := by
      intro p hp
      change (W' p).carrier ⊆ B2.carrier
      rw [hB2_red]
      exact rigidProduct_carrier_subset_closedBall_two (s := s) T hT_ball J ω hω p
        (Finset.mem_product.mp hp).1
    have hdensB2_eq : densityIn s' W' B2 =
        (∑ p ∈ s', volume (W' p).carrier) / volume B2.carrier :=
      densityIn_of_all_le hW'_le_B2
    have hlow_num : (J : ENNReal) * (s.card : ENNReal) *
          ((Tube.le_volume.c n : ENNReal) * δp) ≤
        ∑ p ∈ s', volume (W' p).carrier := by
      simpa [s', W', δp, n] using sum_volume_rigidProduct_ge (s := s) T J ω
    have hLB : (J : ENNReal) * (s.card : ENNReal) *
          ((Tube.le_volume.c n : ENNReal) * δp) / volume B2.carrier ≤
        densityIn s' W' B2 := by
      rw [hdensB2_eq]
      exact ENNReal.div_le_div hlow_num (le_refl _)
    have hδr : 0 < (δ : ℝ) := by exact_mod_cast hδ_pos
    have hδm_nn : 0 ≤ (δ : ℝ) ^ (-η) := by positivity
    have hJ_nn : 0 ≤ (J : ℝ) := le_of_lt (by exact_mod_cast hJ)
    have hclb_nn : 0 ≤ (Tube.le_volume.c n : ℝ) := by exact NNReal.coe_nonneg _
    have hCC_nn : 0 ≤ CC := by
      exact bot_le
    have hL : (ENNReal.ofReal C_cover * (ENNReal.ofReal (A * (s.card : ℝ)) * Dcap)) *
            volume B2.carrier =
          ENNReal.ofReal (C_cover * (A * (s.card : ℝ)) * volume.real B2.carrier *
            (Tube.volume_le.C n : ℝ)) * δp := by
      rw [← hvolB2_ofReal]
      have hCub : (Tube.volume_le.C n : ENNReal) =
          ENNReal.ofReal (Tube.volume_le.C n : ℝ) := by
        exact (ENNReal.ofReal_coe_nnreal (p := Tube.volume_le.C n)).symm
      have hDcap : Dcap = ENNReal.ofReal (Tube.volume_le.C n : ℝ) * δp := by
        dsimp [Dcap]
        exact congrArg (fun x : ENNReal => x * δp) hCub
      rw [hDcap]
      calc
        ENNReal.ofReal C_cover * (ENNReal.ofReal (A * (s.card : ℝ)) *
            (ENNReal.ofReal (Tube.volume_le.C n : ℝ) * δp)) *
            ENNReal.ofReal (volume.real B2.carrier)
            = ENNReal.ofReal C_cover * ENNReal.ofReal (A * (s.card : ℝ)) *
                ENNReal.ofReal (volume.real B2.carrier) *
                ENNReal.ofReal (Tube.volume_le.C n : ℝ) * δp := by ring
        _ = ENNReal.ofReal (C_cover * (A * (s.card : ℝ)) *
                volume.real B2.carrier * (Tube.volume_le.C n : ℝ)) * δp := by
              rw [← ENNReal.ofReal_mul hC_cover_nn]
              rw [← ENNReal.ofReal_mul (mul_nonneg hC_cover_nn hA_mul_nn)]
              rw [← ENNReal.ofReal_mul
                (mul_nonneg (mul_nonneg hC_cover_nn hA_mul_nn) hvB2r_nn)]
    have hR : CC * ((J : ENNReal) * (s.card : ENNReal) *
          ((Tube.le_volume.c n : ENNReal) * δp)) =
          ENNReal.ofReal ((δ : ℝ)^(-η) * (J : ℝ) * (s.card : ℝ) *
            (Tube.le_volume.c n : ℝ)) * δp := by
      dsimp [CC]
      have hJ : (J : ENNReal) = ENNReal.ofReal (J : ℝ) := by simp
      have hS : (s.card : ENNReal) = ENNReal.ofReal (s.card : ℝ) := by simp
      have hclb : (Tube.le_volume.c n : ENNReal) =
          ENNReal.ofReal (Tube.le_volume.c n : ℝ) := by
        exact (ENNReal.ofReal_coe_nnreal (p := Tube.le_volume.c n)).symm
      rw [hJ, hS, hclb]
      calc
        ENNReal.ofReal ((δ : ℝ)^(-η)) * (ENNReal.ofReal (J : ℝ) *
            ENNReal.ofReal (s.card : ℝ) *
            (ENNReal.ofReal (Tube.le_volume.c n : ℝ) * δp))
            = ENNReal.ofReal ((δ : ℝ)^(-η)) * ENNReal.ofReal (J : ℝ) *
                ENNReal.ofReal (s.card : ℝ) *
                ENNReal.ofReal (Tube.le_volume.c n : ℝ) * δp := by ring
        _ = ENNReal.ofReal ((δ : ℝ)^(-η) * (J : ℝ) * (s.card : ℝ) *
                (Tube.le_volume.c n : ℝ)) * δp := by
              rw [← ENNReal.ofReal_mul hδm_nn]
              rw [← ENNReal.ofReal_mul (mul_nonneg hδm_nn hJ_nn)]
              rw [← ENNReal.ofReal_mul
                (mul_nonneg (mul_nonneg hδm_nn hJ_nn) hs_card_nn)]
    have hcmp : ENNReal.ofReal (C_cover * (A * (s.card : ℝ)) *
            volume.real B2.carrier * (Tube.volume_le.C n : ℝ)) * δp ≤
          ENNReal.ofReal ((δ : ℝ)^(-η) * (J : ℝ) * (s.card : ℝ) *
            (Tube.le_volume.c n : ℝ)) * δp := by
      rw [ENNReal.mul_le_mul_iff_left hδp_ne0 hδp_neTop]
      exact ENNReal.ofReal_le_ofReal (by
        nlinarith [mul_le_mul_of_nonneg_right hA hs_card_nn])
    have hprod : (ENNReal.ofReal C_cover *
          (ENNReal.ofReal (A * (s.card : ℝ)) * Dcap)) * volume B2.carrier ≤
        CC * ((J : ENNReal) * (s.card : ENNReal) *
          ((Tube.le_volume.c n : ENNReal) * δp)) := by
      rw [hL]
      rw [show CC * ((J : ENNReal) * (s.card : ENNReal) *
            ((Tube.le_volume.c n : ENNReal) * δp)) =
            ENNReal.ofReal ((δ : ℝ)^(-η) * (J : ℝ) * (s.card : ℝ) *
              (Tube.le_volume.c n : ℝ)) * δp by exact hR]
      exact hcmp
    have hARITH : ENNReal.ofReal C_cover *
          (ENNReal.ofReal (A * (s.card : ℝ)) * Dcap) ≤
        CC * ((J : ENNReal) * (s.card : ENNReal) *
          ((Tube.le_volume.c n : ENNReal) * δp) / volume B2.carrier) := by
      rw [← mul_div_assoc]
      rw [ENNReal.le_div_iff_mul_le (h0 := Or.inl hvolB2_ne0)
        (ht := Or.inl hvolB2_neTop)]
      exact hprod
    calc
      densityIn s' W' K₀ ≤ ENNReal.ofReal C_cover * densityIn s' W' K := hcoverK0
      _ ≤ ENNReal.ofReal C_cover *
            (ENNReal.ofReal (A * (s.card : ℝ)) * Dcap) :=
            mul_le_mul_of_nonneg_left hUK bot_le
      _ ≤ CC * ((J : ENNReal) * (s.card : ENNReal) *
            ((Tube.le_volume.c n : ENNReal) * δp) / volume B2.carrier) := hARITH
      _ ≤ CC * densityIn s' W' B2 := mul_le_mul_of_nonneg_left hLB hCC_nn

/-! ## The Frostman-good event -/

/-- The dimensional constant that absorbs the Frostman-conjunct residual once the factor `J` has
cancelled: `C₁₀₈ + M_vol / (c_vol · |B₁|) + 1`, where `C₁₀₈` is the constant of GWZ (108). -/
def frostmanCapConstant (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (C108 : ℝ) : ℝ :=
  C108 + (Tube.volume_le.C (Module.finrank ℝ E) : ℝ) /
      ((Tube.le_volume.c (Module.finrank ℝ E) : ℝ) *
        volume.real (ConvexSpaceBody.closedUnitBall (E := E)).carrier) + 1

/-- **The translation part of a random rigid tuple lies in the unit ball almost surely.**
`uniformBallMeasure` is Lebesgue measure restricted to `B₁` and renormalised, so its complement is
null; the rotational factor is irrelevant. -/
theorem rigidPiMeasure_translation_outside_eq_zero (J : ℕ) :
    rigidPiMeasure E J
        {ω : Fin J → unitary (E →L[ℝ] E) × E | ∃ j, (ω j).2 ∉ closedBall (0 : E) 1} = 0 := by
  classical
  let B : Set (unitary (E →L[ℝ] E) × E) :=
    {p : unitary (E →L[ℝ] E) × E | p.2 ∉ closedBall (0 : E) 1}
  have hB_eq : B = Prod.snd ⁻¹' (closedBall (0 : E) 1)ᶜ := by
    ext p
    dsimp [B]
    simp
  have hB_meas : MeasurableSet B := by
    rw [hB_eq]
    exact measurableSet_preimage
      (measurable_snd (α := unitary (E →L[ℝ] E)) (β := E))
      isClosed_closedBall.measurableSet.compl
  have hmp_eval : ∀ j : Fin J,
      MeasurePreserving (Function.eval j) (rigidPiMeasure E J) (rigidMeasure E) := by
    intro j
    rw [rigidPiMeasure]
    exact measurePreserving_eval (μ := fun _ : Fin J => rigidMeasure E) j
  have hmap_eval : ∀ j : Fin J,
      rigidPiMeasure E J ((Function.eval j) ⁻¹' B) = rigidMeasure E B := by
    intro j
    calc
      rigidPiMeasure E J ((Function.eval j) ⁻¹' B)
          = (rigidPiMeasure E J).map (Function.eval j) B :=
            (Measure.map_apply (μ := rigidPiMeasure E J)
              (measurable_pi_apply j) hB_meas).symm
      _ = rigidMeasure E B := by rw [(hmp_eval j).map_eq]
  have huniform : uniformBallMeasure E ((closedBall (0 : E) 1)ᶜ) = 0 := by
    rw [uniformBallMeasure, Measure.smul_apply,
      Measure.restrict_apply (isClosed_closedBall.measurableSet.compl)]
    simp
  have hrm : rigidMeasure E B = 0 := by
    dsimp [B]
    have hset : {p : unitary (E →L[ℝ] E) × E | p.2 ∉ closedBall (0 : E) 1} =
        Set.univ ×ˢ (closedBall (0 : E) 1)ᶜ := by
      ext p
      simp
    rw [rigidMeasure, hset, Measure.prod_prod]
    simp [huniform]
  rw [Set.setOf_exists]
  rw [measure_iUnion_null_iff]
  intro j
  rw [show {ω : Fin J → unitary (E →L[ℝ] E) × E | (ω j).2 ∉ closedBall (0 : E) 1} =
      (Function.eval j) ⁻¹' B by
    ext ω
    dsimp [B]
    simp]
  rw [hmap_eval j]
  exact hrm

/-- **The test family, transported to the randomised family.**

`Kakeya.exists_netF_test_family` produces `NetF` from `δ` alone, before the family is quantified,
which is exactly what lets a single `NetF` serve a family whose rigid motions are chosen afterwards.
Combined with `Kakeya.le_maxDensity`, its maximal-density conclusion gives the covering property in
the form `Kakeya.isFrostmanIn_rigidProduct_of_count_le` consumes. -/
theorem exists_netF_cover_rigidProduct [Nontrivial E] (hδ_pos : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ NetF : Finset (ConvexSpaceBody E),
      ((NetF.card : ℝ) ≤ netGeomConstantC E * (δ : ℝ) ^ (-netGeomConstantMRaw E)) ∧
      ∀ {ι : Type*} (s : Finset ι) (T : ι → ShadedTube δ E),
        (∀ i ∈ s, (T i).carrier ⊆ closedBall (0 : E) 1) →
        ∀ (J : ℕ) (ω : Fin J → unitary (E →L[ℝ] E) × E),
          (∀ j, (ω j).2 ∈ closedBall (0 : E) 1) →
          ∀ K' : ConvexSpaceBody E,
            K' ≤ ConvexSpaceBody.cthickening 1 (ConvexSpaceBody.closedUnitBall (E := E)) →
            ∃ K ∈ NetF,
              densityIn (s ×ˢ (Finset.univ : Finset (Fin J)))
                  (fun p => (rigidProduct T J ω p).toConvexSpaceBody) K'
                ≤ ENNReal.ofReal (netGeomConstantC E) *
                  densityIn (s ×ˢ (Finset.univ : Finset (Fin J)))
                    (fun p => (rigidProduct T J ω p).toConvexSpaceBody) K := by
  obtain ⟨NetF, hsub, hcard, hmain⟩ := exists_netF_test_family E hδ_pos hδ1
  refine ⟨NetF, hcard, ?_⟩
  intro ι s T hT_ball J ω hω K' hK'
  have hmem : ∀ p ∈ (s ×ˢ (Finset.univ : Finset (Fin J))),
      (rigidProduct T J ω p).toConvexSpaceBody.carrier ⊆ Metric.closedBall (0 : E) 2 := by
    intro p hp
    exact rigidProduct_carrier_subset_closedBall_two (s := s) T hT_ball J ω hω p
      (Finset.mem_product.mp hp).1
  have hthick : ∀ p ∈ (s ×ˢ (Finset.univ : Finset (Fin J))),
      (δ : ENNReal) ≤ Metric.ethickness.scale ℝ
        (rigidProduct T J ω p).toConvexSpaceBody.carrier := by
    intro p hp
    exact Tube.le_ethickness_scale (rigidProduct T J ω p).toTube
  obtain ⟨K, hK_mem, hK_le⟩ :=
    hmain (s ×ˢ (Finset.univ : Finset (Fin J)))
      (fun p : ι × Fin J => (rigidProduct T J ω p).toConvexSpaceBody) hmem hthick
  exact ⟨K, hK_mem, (le_maxDensity
    (s ×ˢ (Finset.univ : Finset (Fin J)))
    (fun p : ι × Fin J => (rigidProduct T J ω p).toConvexSpaceBody) K').trans hK_le⟩

/-! ### The dimensional constants of the Frostman cap -/

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The upper tube-volume constant is positive. -/
theorem tube_volume_le_C_pos_real :
    0 < (Tube.volume_le.C (Module.finrank ℝ E) : ℝ) := by
  unfold Tube.volume_le.C
  push_cast
  positivity

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The lower tube-volume constant is positive. -/
theorem tube_le_volume_c_pos_real :
    0 < (Tube.le_volume.c (Module.finrank ℝ E) : ℝ) := by
  exact NNReal.coe_pos.mpr (Tube.le_volume.c_pos _)

/-- The unit ball has positive finite volume. -/
theorem volumeReal_closedUnitBall_pos :
    0 < volume.real (ConvexSpaceBody.closedUnitBall (E := E)).carrier := by
  have hpos : (0 : ENNReal) < volume (ConvexSpaceBody.closedUnitBall (E := E)).carrier :=
    ConvexSpaceBody.closedUnitBall_volume_pos
  have hne_top : volume (ConvexSpaceBody.closedUnitBall (E := E)).carrier ≠ ⊤ :=
    (ConvexSpaceBody.closedUnitBall (E := E)).isCompact'.measure_lt_top.ne
  exact ENNReal.toReal_pos hpos.ne' hne_top

theorem lt_frostmanCapConstant {C108 : ℝ} : C108 < frostmanCapConstant E C108 := by
  unfold frostmanCapConstant
  have hC : 0 < (Tube.volume_le.C (Module.finrank ℝ E) : ℝ) := tube_volume_le_C_pos_real
  have hc : 0 < (Tube.le_volume.c (Module.finrank ℝ E) : ℝ) := tube_le_volume_c_pos_real
  have hv : 0 < volume.real (ConvexSpaceBody.closedUnitBall (E := E)).carrier :=
    volumeReal_closedUnitBall_pos
  have hq : 0 < (Tube.volume_le.C (Module.finrank ℝ E) : ℝ) /
      ((Tube.le_volume.c (Module.finrank ℝ E) : ℝ) *
        volume.real (ConvexSpaceBody.closedUnitBall (E := E)).carrier) :=
    div_pos hC (mul_pos hc hv)
  nlinarith [hq]

theorem frostmanCapConstant_pos {C108 : ℝ} (hC108 : 0 < C108) :
    0 < frostmanCapConstant E C108 := lt_trans hC108 lt_frostmanCapConstant

/-- Real-valued comparability of tube volumes, the form the Frostman packing count consumes. -/
theorem tube_volumeReal_bounds [Nontrivial E] (hδ1 : δ ≤ 1) (T₁ : Tube δ E) :
    (Tube.le_volume.c (Module.finrank ℝ E) : ℝ) * (δ : ℝ) ^ (Module.finrank ℝ E - 1)
        ≤ volume.real T₁.carrier ∧
      volume.real T₁.carrier
        ≤ (Tube.volume_le.C (Module.finrank ℝ E) : ℝ) * (δ : ℝ) ^ (Module.finrank ℝ E - 1) := by
  refine ⟨?_, ?_⟩
  · have h := Tube.le_volume T₁
    have hreal := ENNReal.toReal_mono T₁.isCompact.measure_lt_top.ne h
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.coe_toReal,
      ENNReal.coe_toReal] at hreal
    exact hreal
  · have h := Tube.volume_le hδ1 T₁
    have hRHS_fin : (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal) *
        (δ : ENNReal) ^ (Module.finrank ℝ E - 1) ≠ ⊤ := by
      exact ENNReal.mul_ne_top ENNReal.coe_ne_top
        (ENNReal.pow_ne_top ENNReal.coe_ne_top)
    have hreal := ENNReal.toReal_mono hRHS_fin h
    simpa [ENNReal.toReal_mul, ENNReal.coe_toReal,
      ENNReal.toReal_pow, MeasureTheory.Measure.real] using hreal

/-- **The deterministic cap on one rigid copy, with the Frostman constant absorbed into `J`.**

This is `Kakeya.rigidCountIn_le_frostman_packing` with `C_F ≤ J` substituted and the resulting
dimensional quotient bounded by `frostmanCapConstant`. It is what makes the Chernoff cap free of the
Frostman constant. -/
theorem rigidCountIn_le_cap [Nontrivial E] (hδ_pos : 0 < δ) (hδ1 : δ ≤ 1)
    (C108 : ℝ) (hC108 : 0 < C108)
    {ι : Type*} (s : Finset ι) (T : ι → ShadedTube δ E)
    (hT_in_B1 : ∀ i ∈ s, (T i).toConvexSpaceBody ≤ ConvexSpaceBody.closedUnitBall)
    (CF : ℝ) (hCF1 : 1 ≤ CF)
    (hFrost : ConvexSpaceBody.IsFrostmanIn s (fun i => (T i).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall (ENNReal.ofReal CF))
    (J : ℕ) (hJ_ge : CF ≤ (J : ℝ))
    (K : ConvexSpaceBody E) (ω : unitary (E →L[ℝ] E) × E) :
    ((rigidCountIn s (fun i => (T i).toTube) K ω : ℕ) : ℝ)
      ≤ frostmanCapConstant E C108 * (J : ℝ) * (s.card : ℝ) * volume.real K.carrier := by
  classical
  set Cub : ℝ := (Tube.volume_le.C (Module.finrank ℝ E) : ℝ)
  set clb : ℝ := (Tube.le_volume.c (Module.finrank ℝ E) : ℝ)
  set volB1 : ℝ := volume.real (ConvexSpaceBody.closedUnitBall (E := E)).carrier
  have hδ_r : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ_pos
  have hCF_nn : 0 ≤ CF := by exact le_trans (by norm_num) hCF1
  have hclb_pos : 0 < clb := by
    dsimp [clb]
    exact tube_le_volume_c_pos_real
  have hCub_pos : 0 < Cub := by
    dsimp [Cub]
    exact tube_volume_le_C_pos_real
  have hCub_nn : 0 ≤ Cub := le_of_lt hCub_pos
  have hvol_pos : 0 < volB1 := by
    dsimp [volB1]
    exact volumeReal_closedUnitBall_pos
  have hT_lb : ∀ i ∈ s, clb * (δ : ℝ) ^ (Module.finrank ℝ E - 1) ≤ volume.real (T i).carrier := by
    intro i _
    simpa [clb] using (tube_volumeReal_bounds hδ1 (T i).toTube).1
  have hT_ub : ∀ i ∈ s, volume.real (T i).carrier ≤ Cub * (δ : ℝ) ^ (Module.finrank ℝ E - 1) := by
    intro i _
    simpa [Cub] using (tube_volumeReal_bounds hδ1 (T i).toTube).2
  have hdiv_pos : 0 < clb * volB1 := mul_pos hclb_pos hvol_pos
  have hP := rigidCountIn_le_frostman_packing hδ_r s T CF hCF_nn hFrost hT_in_B1
    clb Cub hclb_pos hCub_nn hT_lb hT_ub K ω
  have hDiv : ((rigidCountIn s (fun i => (T i).toTube) K ω : ℕ) : ℝ)
      ≤ (CF * Cub * (s.card : ℝ) * volume.real K.carrier) / (clb * volB1) := by
    rw [le_div_iff₀ hdiv_pos]
    simpa [volB1] using hP
  set A : ℝ := CF * Cub / (clb * volB1)
  have hA3 : ((rigidCountIn s (fun i => (T i).toTube) K ω : ℕ) : ℝ)
      ≤ A * (s.card : ℝ) * volume.real K.carrier := by
    calc
      ((rigidCountIn s (fun i => (T i).toTube) K ω : ℕ) : ℝ)
          ≤ (CF * Cub * (s.card : ℝ) * volume.real K.carrier) / (clb * volB1) := hDiv
      _ = A * (s.card : ℝ) * volume.real K.carrier := by
        dsimp [A]
        ring
  have hq_nn : 0 ≤ Cub / (clb * volB1) :=
    div_nonneg (le_of_lt hCub_pos) (le_of_lt hdiv_pos)
  have hq_le : Cub / (clb * volB1) ≤ frostmanCapConstant E C108 := by
    unfold frostmanCapConstant
    dsimp [Cub, clb, volB1]
    nlinarith [hC108]
  have hA0 : A ≤ frostmanCapConstant E C108 * (J : ℝ) := by
    dsimp [A]
    calc
      CF * Cub / (clb * volB1) = CF * (Cub / (clb * volB1)) := by ring
      _ ≤ (J : ℝ) * frostmanCapConstant E C108 := by
        exact mul_le_mul hJ_ge hq_le hq_nn (Nat.cast_nonneg J)
      _ = frostmanCapConstant E C108 * (J : ℝ) := by ring
  exact calc
    ((rigidCountIn s (fun i => (T i).toTube) K ω : ℕ) : ℝ)
        ≤ A * (s.card : ℝ) * volume.real K.carrier := hA3
    _ ≤ (frostmanCapConstant E C108 * (J : ℝ)) * (s.card : ℝ) * volume.real K.carrier := by
      have hA0' : A * (s.card : ℝ) ≤
          (frostmanCapConstant E C108 * (J : ℝ)) * (s.card : ℝ) :=
        mul_le_mul_of_nonneg_right hA0 (Nat.cast_nonneg s.card)
      exact mul_le_mul_of_nonneg_right hA0' (by positivity)
    _ = frostmanCapConstant E C108 * (J : ℝ) * (s.card : ℝ) * volume.real K.carrier := by rfl

/-- **Per-test-body Chernoff bound for the Frostman conjunct.**

The cap is `M_K := C_cap · J · |s| · |K|` with `C_cap := frostmanCapConstant E C₁₀₈`. It dominates
the deterministic Frostman packing bound because `C_F ≤ J`, and it strictly dominates
`J · 𝔼[X_j] = J · |s| · C₁₀₈ · |K|` because `C₁₀₈ < C_cap`. With threshold `S := L · M_K` the ratio
`S / M_K` is exactly `L`, so the tail is `exp (10e - L)` — independent of `K`, of the family, and of
the Frostman constant. -/
theorem rigid_frostman_per_body_tail [Nontrivial E] (hδ_pos : 0 < δ) (hδ1 : δ ≤ 1)
    (C108 : ℝ) (hC108 : 0 < C108)
    (hP : ∀ (T₁ : Tube δ E) (K : ConvexSpaceBody E),
      (rigidMeasure E {ω : unitary (E →L[ℝ] E) × E |
          (T₁.rigidMove ω.1 ω.2).carrier ⊆ K.carrier}).toReal
        ≤ C108 * volume.real K.carrier)
    {ι : Type*} (s : Finset ι) (T : ι → ShadedTube δ E) (hs_card : 0 < s.card)
    (hT_in_B1 : ∀ i ∈ s, (T i).toConvexSpaceBody ≤ ConvexSpaceBody.closedUnitBall)
    (CF : ℝ) (hCF1 : 1 ≤ CF)
    (hFrost : ConvexSpaceBody.IsFrostmanIn s (fun i => (T i).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall (ENNReal.ofReal CF))
    (J : ℕ) (hJ : 0 < J) (hJ_ge : CF ≤ (J : ℝ))
    (K : ConvexSpaceBody E) (hK_vol : 0 < volume.real K.carrier) (L : ℝ) :
    (rigidPiMeasure E J
        {ω : Fin J → unitary (E →L[ℝ] E) × E |
          L * (frostmanCapConstant E C108 * (J : ℝ) * (s.card : ℝ) * volume.real K.carrier)
            < ∑ j : Fin J, rigidCountInAt s (fun i => (T i).toTube) K J j ω}).toReal
      ≤ Real.exp (10 * Real.exp 1 - L) := by
  classical
  set Tt : ι → Tube δ E := fun i => (T i).toTube
  set M : ℝ := frostmanCapConstant E C108 * (J : ℝ) * (s.card : ℝ)
    * volume.real K.carrier with hM
  have hJpos : 0 < (J : ℝ) := by exact_mod_cast hJ
  have hsc_pos : 0 < (s.card : ℝ) := by exact_mod_cast hs_card
  have hVK_pos : 0 < volume.real K.carrier := hK_vol
  have hcap_pos : 0 < frostmanCapConstant E C108 :=
    frostmanCapConstant_pos (E := E) hC108
  have hM_pos : 0 < M := by
    rw [hM]
    exact mul_pos (mul_pos (mul_pos hcap_pos hJpos) hsc_pos) hVK_pos
  have hp : ∀ i ∈ s,
      (rigidMeasure E {ω : unitary (E →L[ℝ] E) × E |
          ((Tt i).rigidMove ω.1 ω.2).carrier ⊆ K.carrier}).toReal
        ≤ C108 * volume.real K.carrier := by
    intro i hi
    simpa [Tt] using hP (Tt i) K
  have hXM : ∀ (j : Fin J) (ω : Fin J → unitary (E →L[ℝ] E) × E),
      rigidCountInAt s Tt K J j ω ≤ M := by
    intro j ω'
    dsimp [Tt]
    exact rigidCountIn_le_cap hδ_pos hδ1 C108 hC108 s T hT_in_B1 CF hCF1 hFrost J
      hJ_ge K (ω' j)
  have hJmM : (J : ℝ) * ((s.card : ℝ) * (C108 * volume.real K.carrier)) < M := by
    rw [hM]
    have hlt : C108 < frostmanCapConstant E C108 := lt_frostmanCapConstant (E := E)
    have hprod : 0 < (J : ℝ) * (s.card : ℝ) * volume.real K.carrier :=
      mul_pos (mul_pos hJpos hsc_pos) hVK_pos
    have hlt' : (J : ℝ) * (s.card : ℝ) * volume.real K.carrier * C108
        < (J : ℝ) * (s.card : ℝ) * volume.real K.carrier * frostmanCapConstant E C108 :=
      mul_lt_mul_of_pos_left hlt hprod
    nlinarith [hlt']
  have hres : (rigidPiMeasure E J
      {ω : Fin J → (unitary (E →L[ℝ] E) × E) |
        ∑ j : Fin J, rigidCountInAt s Tt K J j ω > L * M}).toReal
      ≤ Real.exp (10 * Real.exp 1 - (L * M) / M) :=
    rigidCountIn_chernoff_tail s Tt K hJ M hM_pos hXM (C108 * volume.real K.carrier)
      hp hJmM (L * M)
  have hdiv : (L * M) / M = L := by
    rw [mul_div_assoc, div_self hM_pos.ne', mul_one]
  simpa [gt_iff_lt, Tt, hdiv] using hres

/-- **The `C_F`-free smallness condition on `δ`.**

This is the hypothesis `hA` of `Kakeya.isFrostmanIn_rigidProduct_of_count_le` after the two factors
of `J` have cancelled. Every quantity in it is dimensional except the threshold multiplier
`rigidMED (1 · edNetCalibration E) δ`, which is `O(log (1/δ))`, so
`Kakeya.eventually_le_rpow_neg_of_le_polylog` absorbs it into `δ^(-η)`. In particular the resulting
eventual `δ`-set depends only on `η` and on the ambient dimension. -/
theorem eventually_frostman_threshold [Nontrivial E] {η : ℝ} (hη : 0 < η)
    (Ccap : ℝ) (hCcap : 0 < Ccap) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ((rigidMED (1 * edNetCalibration E) δ : ℕ) : ℝ) * Ccap
          * (Tube.volume_le.C (Module.finrank ℝ E) : ℝ) * netGeomConstantC E
          * volume.real
              (ConvexSpaceBody.cthickening 1 (ConvexSpaceBody.closedUnitBall (E := E))).carrier
        ≤ (δ : ℝ) ^ (-η) * (Tube.le_volume.c (Module.finrank ℝ E) : ℝ) := by
  let cal : ℝ := 1 * edNetCalibration E
  let Cub : ℝ := (Tube.volume_le.C (Module.finrank ℝ E) : ℝ)
  let clb : ℝ := (Tube.le_volume.c (Module.finrank ℝ E) : ℝ)
  let Cnet : ℝ := netGeomConstantC E
  let volB2 : ℝ := volume.real
      (ConvexSpaceBody.cthickening 1 (ConvexSpaceBody.closedUnitBall (E := E))).carrier
  let K0 : ℝ := Ccap * Cub * Cnet * volB2
  have hCub_pos : 0 < Cub := tube_volume_le_C_pos_real
  have hclb_pos : 0 < clb := tube_le_volume_c_pos_real
  have hCnet_pos : 0 < Cnet := netGeomConstantC_pos E
  have hvolB2_pos : 0 < volB2 := by
    dsimp [volB2]
    rw [cthickening_closedUnitBall_carrier (E := E) 1 (by norm_num : (0 : ℝ) ≤ 1)]
    norm_num
    refine ENNReal.toReal_pos ?_ MeasureTheory.measure_closedBall_lt_top.ne
    exact (Metric.measure_closedBall_pos volume (0 : E) (by norm_num : (0 : ℝ) < 2)).ne'
  have hK0_pos : 0 < K0 := by
    dsimp [K0]
    positivity
  have hK0_nn : 0 ≤ K0 := le_of_lt hK0_pos
  have hcal_pos : 0 < cal := by
    dsimp [cal]
    rw [one_mul]
    exact edNetCalibration_pos
  have hcap_pos : 0 < cal + 2 := by nlinarith [hcal_pos]
  have hq_pos : 0 < K0 / clb := div_pos hK0_pos hclb_pos
  have hq_nn : 0 ≤ K0 / clb := le_of_lt hq_pos
  have hC_pos : 0 < (cal + 2) * (K0 / clb) := mul_pos hcap_pos hq_pos
  have hev :
      ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
        ((rigidMED (1 * edNetCalibration E) δ : ℕ) : ℝ) * (K0 / clb) ≤ (δ : ℝ) ^ (-η) := by
    refine eventually_le_rpow_neg_of_le_polylog hC_pos hη 1
      (f := fun δ => ((rigidMED (1 * edNetCalibration E) δ : ℕ) : ℝ) * (K0 / clb)) ?_
    intro δ hδ hδ1
    have hs := rigidMED_le_polylog (C := 1 * edNetCalibration E) hcal_pos δ hδ hδ1
    calc
      ((rigidMED (1 * edNetCalibration E) δ : ℕ) : ℝ) * (K0 / clb)
          ≤ ((cal + 2) * (1 + Real.log (1 / (δ : ℝ))) ^ 1) * (K0 / clb) := by
              exact mul_le_mul_of_nonneg_right (by simpa [cal] using hs) hq_nn
      _ = ((cal + 2) * (K0 / clb)) * (1 + Real.log (1 / (δ : ℝ))) ^ 1 := by ring
  filter_upwards [hev, self_mem_nhdsWithin] with δ hδ hδpos
  have hdiv :
      ((rigidMED (1 * edNetCalibration E) δ : ℕ) : ℝ) * K0 / clb ≤ (δ : ℝ) ^ (-η) := by
    simpa [mul_div_assoc] using hδ
  have hmul :
      ((rigidMED (1 * edNetCalibration E) δ : ℕ) : ℝ) * K0 ≤ (δ : ℝ) ^ (-η) * clb :=
    (div_le_iff₀ hclb_pos).mp hdiv
  calc
    ((rigidMED (1 * edNetCalibration E) δ : ℕ) : ℝ) * Ccap
        * (Tube.volume_le.C (Module.finrank ℝ E) : ℝ) * netGeomConstantC E * volB2
        = ((rigidMED (1 * edNetCalibration E) δ : ℕ) : ℝ) * K0 := by
          dsimp [K0, Cub, Cnet]
          ring
    _ ≤ (δ : ℝ) ^ (-η) * (Tube.le_volume.c (Module.finrank ℝ E) : ℝ) := by
          dsimp [clb] at hmul
          exact hmul

/-- **Per-test-body Chernoff bound for the Frostman conjunct, including null-volume test bodies.**

This is `Kakeya.rigid_frostman_per_body_tail` with the `0 < volume.real K.carrier` hypothesis
removed: when `K` has zero volume the threshold is `0` and every count is `≤ 0`, so the bad event is
empty and its measure is `0 ≤ exp (10e - L)`. -/
private lemma rigid_frostman_per_body_tail' [Nontrivial E] (hδ_pos : 0 < δ) (hδ1 : δ ≤ 1)
    (C108 : ℝ) (hC108 : 0 < C108)
    (hP : ∀ (T₁ : Tube δ E) (K : ConvexSpaceBody E),
      (rigidMeasure E {ω : unitary (E →L[ℝ] E) × E |
          (T₁.rigidMove ω.1 ω.2).carrier ⊆ K.carrier}).toReal
        ≤ C108 * volume.real K.carrier)
    {ι : Type*} (s : Finset ι) (T : ι → ShadedTube δ E) (hs_card : 0 < s.card)
    (hT_in_B1 : ∀ i ∈ s, (T i).toConvexSpaceBody ≤ ConvexSpaceBody.closedUnitBall)
    (CF : ℝ) (hCF1 : 1 ≤ CF)
    (hFrost : ConvexSpaceBody.IsFrostmanIn s (fun i => (T i).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall (ENNReal.ofReal CF))
    (J : ℕ) (hJ : 0 < J) (hJ_ge : CF ≤ (J : ℝ))
    (K : ConvexSpaceBody E) (L : ℝ) :
    (rigidPiMeasure E J
        {ω : Fin J → unitary (E →L[ℝ] E) × E |
          L * (frostmanCapConstant E C108 * (J : ℝ) * (s.card : ℝ) * volume.real K.carrier)
            < ∑ j : Fin J, rigidCountInAt s (fun i => (T i).toTube) K J j ω}).toReal
      ≤ Real.exp (10 * Real.exp 1 - L) := by
  by_cases hKvol : 0 < volume.real K.carrier
  · exact rigid_frostman_per_body_tail hδ_pos hδ1 C108 hC108 hP s T hs_card hT_in_B1 CF hCF1
      hFrost J hJ hJ_ge K hKvol L
  · have hKvol0 : volume.real K.carrier = 0 := by
      exact le_antisymm (le_of_not_gt hKvol) ENNReal.toReal_nonneg
    have hBadOf : {ω : Fin J → unitary (E →L[ℝ] E) × E |
        L * (frostmanCapConstant E C108 * (J : ℝ) * (s.card : ℝ) * volume.real K.carrier)
          < ∑ j : Fin J, rigidCountInAt s (fun i => (T i).toTube) K J j ω} = ∅ := by
      ext ω
      constructor
      · intro hlt
        have hlt0 : (0 : ℝ) < ∑ j : Fin J, rigidCountInAt s (fun i => (T i).toTube) K J j ω := by
          simpa [hKvol0] using hlt
        have hle0 : ∀ j : Fin J, rigidCountInAt s (fun i => (T i).toTube) K J j ω ≤ 0 := by
          intro j
          have hle := rigidCountIn_le_cap hδ_pos hδ1 C108 hC108 s T hT_in_B1 CF hCF1 hFrost J
            hJ_ge K (ω j)
          simpa [rigidCountInAt, hKvol0] using hle
        have hsum : (∑ j : Fin J, rigidCountInAt s (fun i => (T i).toTube) K J j ω) ≤ 0 :=
          Finset.sum_nonpos (fun j _ => hle0 j)
        exact not_lt_of_ge hsum hlt0
      · intro h
        exact False.elim h
    rw [hBadOf]
    simp only [measure_empty, ENNReal.toReal_zero]
    exact le_of_lt (Real.exp_pos _)

/-- **The Frostman-good event has probability more than `3/4`.**

For all sufficiently small `δ` — a threshold depending only on `η` and the ambient dimension, *not*
on the family or on its Frostman constant — the set of rigid tuples for which the randomised family
fails to be `δ^(-η)`-convex-Frostman in `B₂` has probability below `1/4`.

The number of copies `J` is only required to dominate the canonical Frostman constant of the input
family, which is how `J := ⌈C_F⌉₊` is admissible. -/
theorem rigid_frostman_bad_prob_lt [Nontrivial E] (_hn : 1 < Module.finrank ℝ E)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
    ∀ {ι : Type*} (s : Finset ι) (T : ι → ShadedTube δ E),
      (∀ i ∈ s, (T i).carrier ⊆ closedBall (0 : E) 1) →
      0 < s.card →
      ∀ (J : ℕ), 0 < J →
        (ConvexSpaceBody.frostmanConstant s (fun i => (T i).toConvexSpaceBody)
            ConvexSpaceBody.closedUnitBall).toReal ≤ (J : ℝ) →
        rigidPiMeasure E J
            {ω : Fin J → unitary (E →L[ℝ] E) × E |
              ¬ ConvexSpaceBody.IsFrostmanIn (s ×ˢ (Finset.univ : Finset (Fin J)))
                  (fun p => (rigidProduct T J ω p).toConvexSpaceBody)
                  (ConvexSpaceBody.cthickening 1
                    (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E))
                  (ENNReal.ofReal ((δ : ℝ) ^ (-η)))}
          < ENNReal.ofReal (1 / 4) := by
  classical
  obtain ⟨C108E, hC108E_top, hP108⟩ := prob_rigidMove_subset_volume_le (E := E)
  set C108 : ℝ := max C108E.toReal 1
  have hC108 : 0 < C108 := by
    dsimp [C108]
    exact lt_max_of_lt_right (by norm_num)
  set Ccap : ℝ := frostmanCapConstant E C108
  have hCcap : 0 < Ccap := frostmanCapConstant_pos (E := E) hC108
  have hlt1 : ∀ᶠ (x : ℝ) in 𝓝[>] (0 : ℝ), x < (1 : ℝ) := by
    refine Filter.eventually_of_mem (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)) ?_
    intro x hx
    exact hx.2
  have hδ1ev : ∀ᶠ (δ : NNReal) in 𝓝[>] (0 : NNReal), (δ : ℝ) ≤ 1 := by
    filter_upwards [nnreal_eventually_of_real_eventually hlt1] with δ hδlt
    exact le_of_lt hδlt
  filter_upwards [self_mem_nhdsWithin, hδ1ev,
      eventually_frostman_threshold (E := E) hη Ccap hCcap]
    with δ hδpos hδ1 hδsmall
  intro ι s T hT_ball hs_card J hJ hJ_ge
  obtain ⟨NetF, hNetF_card, hNetF_cover⟩ := exists_netF_cover_rigidProduct (E := E) hδpos hδ1
  set L : ℝ := ((rigidMED (1 * edNetCalibration E) δ : ℕ) : ℝ)
  set A : ℝ := L * Ccap * (J : ℝ)
  let volB2 : ℝ := volume.real
      (ConvexSpaceBody.cthickening 1 (ConvexSpaceBody.closedUnitBall (E := E))).carrier
  have hA_nn : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (le_of_lt hCcap)) (Nat.cast_nonneg J)
  have hP : ∀ (T₁ : Tube δ E) (K : ConvexSpaceBody E),
      (rigidMeasure E {ω : unitary (E →L[ℝ] E) × E |
          (T₁.rigidMove ω.1 ω.2).carrier ⊆ K.carrier}).toReal
        ≤ C108 * volume.real K.carrier := by
    intro T₁ K
    have hle := hP108 T₁ K
    have htop : C108E * volume K.carrier ≠ ⊤ := by
      exact ENNReal.mul_ne_top hC108E_top K.isCompact'.measure_lt_top.ne
    have hreal := ENNReal.toReal_mono htop hle
    have hreal' : (rigidMeasure E {ω : unitary (E →L[ℝ] E) × E |
          (T₁.rigidMove ω.1 ω.2).carrier ⊆ K.carrier}).toReal
        ≤ C108E.toReal * volume.real K.carrier := by
      rw [ENNReal.toReal_mul] at hreal
      simpa [MeasureTheory.Measure.real] using hreal
    have hC108E_le : C108E.toReal ≤ C108 := by
      dsimp [C108]
      exact le_max_left _ _
    exact le_trans hreal' (mul_le_mul_of_nonneg_right hC108E_le ENNReal.toReal_nonneg)
  have hT_in_B1 : ∀ i ∈ s, (T i).toConvexSpaceBody ≤ ConvexSpaceBody.closedUnitBall (E := E) := by
    intro i hi x hx
    have hx_carr : x ∈ (T i).carrier := hx
    have hball : x ∈ Metric.closedBall (0 : E) 1 := hT_ball i hi hx_carr
    change x ∈ (ConvexSpaceBody.closedUnitBall (E := E)).carrier
    rw [ConvexSpaceBody.closedUnitBall_carrier]
    exact hball
  let CF : ℝ := max (ConvexSpaceBody.frostmanConstant s (fun i => (T i).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall).toReal 1
  have hCF1 : 1 ≤ CF := by
    dsimp [CF]
    exact le_max_right _ _
  have hFrost : ConvexSpaceBody.IsFrostmanIn s (fun i => (T i).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall (ENNReal.ofReal CF) := by
    let CF0 : ENNReal := ConvexSpaceBody.frostmanConstant s (fun i => (T i).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall
    have hne : CF0 ≠ ⊤ := by
      dsimp [CF0]
      exact Tube.frostmanConstant_ne_top hδpos s (fun i => (T i).toTube) hT_ball
    have hofReal : ENNReal.ofReal CF0.toReal = CF0 := ENNReal.ofReal_toReal hne
    have hle : CF0 ≤ ENNReal.ofReal CF := by
      rw [← hofReal]
      exact ENNReal.ofReal_le_ofReal (by
        dsimp [CF, CF0]
        exact le_max_left _ _)
    rw [← ConvexSpaceBody.frostmanConstant_le_iff]
    exact hle
  have hJ_ge' : CF ≤ (J : ℝ) := by
    dsimp [CF]
    exact max_le hJ_ge (by exact_mod_cast (Nat.succ_le_of_lt hJ))
  set BadOf : ConvexSpaceBody E → Set (Fin J → unitary (E →L[ℝ] E) × E) := fun K =>
    {ω | L * (Ccap * (J : ℝ) * (s.card : ℝ) * volume.real K.carrier)
         < ∑ j : Fin J, rigidCountInAt s (fun i => (T i).toTube) K J j ω}
  set Out : Set (Fin J → unitary (E →L[ℝ] E) × E) := {ω | ∃ j, (ω j).2 ∉ closedBall (0 : E) 1}
  set Bad := (⋃ K ∈ NetF, BadOf K) ∪ Out
  let FrostBad : Set (Fin J → unitary (E →L[ℝ] E) × E) :=
    {ω | ¬ ConvexSpaceBody.IsFrostmanIn (s ×ˢ (Finset.univ : Finset (Fin J)))
        (fun p => (rigidProduct T J ω p).toConvexSpaceBody)
        (ConvexSpaceBody.cthickening 1 (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E))
        (ENNReal.ofReal ((δ : ℝ) ^ (-η)))}
  have hcontain : FrostBad ⊆ Bad := by
    intro ω hωFrost
    by_contra hnotBad
    have hωnotBadUnion : ω ∉ ⋃ K ∈ NetF, BadOf K := by
      intro hmem
      exact hnotBad (Set.mem_union_left Out hmem)
    have hωnotOut : ω ∉ Out := by
      intro hmem
      exact hnotBad (Set.mem_union_right (⋃ K ∈ NetF, BadOf K) hmem)
    have hω : ∀ j, (ω j).2 ∈ closedBall (0 : E) 1 := by
      intro j
      by_contra hnot
      exact hωnotOut ⟨j, hnot⟩
    have hcount : ∀ K ∈ NetF,
        (∑ j : Fin J, ((rigidCountIn s (fun i => (T i).toTube) K (ω j) : ℕ) : ℝ))
          ≤ A * (s.card : ℝ) * volume.real K.carrier := by
      intro K hK
      have hnotBadK : ω ∉ BadOf K := by
        intro hmem
        exact hωnotBadUnion (Set.mem_biUnion hK hmem)
      have hle : (∑ j : Fin J, rigidCountInAt s (fun i => (T i).toTube) K J j ω)
          ≤ L * (Ccap * (J : ℝ) * (s.card : ℝ) * volume.real K.carrier) := by
        change ¬ (L * (Ccap * (J : ℝ) * (s.card : ℝ) * volume.real K.carrier)
            < ∑ j : Fin J, rigidCountInAt s (fun i => (T i).toTube) K J j ω) at hnotBadK
        exact not_lt.mp hnotBadK
      calc
        (∑ j : Fin J, ((rigidCountIn s (fun i => (T i).toTube) K (ω j) : ℕ) : ℝ))
            = ∑ j : Fin J, rigidCountInAt s (fun i => (T i).toTube) K J j ω := by
              simp [rigidCountInAt]
        _ ≤ L * (Ccap * (J : ℝ) * (s.card : ℝ) * volume.real K.carrier) := hle
        _ = A * (s.card : ℝ) * volume.real K.carrier := by
              dsimp [A]
              ring
    have hA : A * (Tube.volume_le.C (Module.finrank ℝ E) : ℝ) * netGeomConstantC E * volB2
        ≤ (δ : ℝ) ^ (-η) * (J : ℝ) * (Tube.le_volume.c (Module.finrank ℝ E) : ℝ) := by
      have hJnn : 0 ≤ (J : ℝ) := by exact_mod_cast (le_of_lt hJ)
      calc
        A * (Tube.volume_le.C (Module.finrank ℝ E) : ℝ) * netGeomConstantC E * volB2
            = (J : ℝ) * (L * Ccap * (Tube.volume_le.C (Module.finrank ℝ E) : ℝ)
                * netGeomConstantC E * volB2) := by
              dsimp [A]
              ring
        _ ≤ (J : ℝ) * ((δ : ℝ) ^ (-η) * (Tube.le_volume.c (Module.finrank ℝ E) : ℝ)) := by
              simpa [L, volB2] using mul_le_mul_of_nonneg_left hδsmall hJnn
        _ = (δ : ℝ) ^ (-η) * (J : ℝ) * (Tube.le_volume.c (Module.finrank ℝ E) : ℝ) := by ring
    have hFrost : ConvexSpaceBody.IsFrostmanIn (s ×ˢ (Finset.univ : Finset (Fin J)))
        (fun p => (rigidProduct T J ω p).toConvexSpaceBody)
        (ConvexSpaceBody.cthickening 1 (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E))
        (ENNReal.ofReal ((δ : ℝ) ^ (-η))) := by
      exact isFrostmanIn_rigidProduct_of_count_le hδpos hδ1 s T hT_ball hs_card J hJ ω hω
        NetF (netGeomConstantC E) (netGeomConstantC_pos E) (hNetF_cover s T hT_ball J ω hω)
        hA_nn hcount hA
    exact hωFrost hFrost
  let μ : Measure (Fin J → unitary (E →L[ℝ] E) × E) := rigidPiMeasure E J
  have hμuniv : μ Set.univ = 1 := by
    simp [μ]
  haveI : IsFiniteMeasure μ := by
    constructor
    rw [hμuniv]
    exact ENNReal.coe_lt_top
  let EXP : ℝ := Real.exp (10 * Real.exp 1 - L)
  have hOut : μ Out = 0 := by
    simpa [μ, Out] using rigidPiMeasure_translation_outside_eq_zero (E := E) J
  have hTailB : ∀ K ∈ NetF, (μ (BadOf K)).toReal ≤ EXP := by
    intro K hK
    have htail := rigid_frostman_per_body_tail' hδpos hδ1 C108 hC108 hP s T hs_card hT_in_B1 CF
      hCF1 hFrost J hJ hJ_ge' K L
    simpa [μ, BadOf, EXP, Ccap] using htail
  have hsum : (∑ K ∈ NetF, (μ (BadOf K)).toReal) ≤ (NetF.card : ℝ) * EXP := by
    calc
      (∑ K ∈ NetF, (μ (BadOf K)).toReal) ≤ ∑ K ∈ NetF, EXP := by
        exact Finset.sum_le_sum (fun K hK => hTailB K hK)
      _ = (NetF.card : ℝ) * EXP := by
        simp [Finset.sum_const]
  have htoRealUnion : (μ (⋃ K ∈ NetF, BadOf K)).toReal ≤ (NetF.card : ℝ) * EXP := by
    have hBunion : μ (⋃ K ∈ NetF, BadOf K) ≤ ∑ K ∈ NetF, μ (BadOf K) :=
      measure_biUnion_finset_le NetF BadOf
    have hSn : (∑ K ∈ NetF, μ (BadOf K)) ≠ (⊤ : ENNReal) := by
      rw [ENNReal.sum_ne_top]
      intro K hK
      exact measure_ne_top μ (BadOf K)
    calc
      (μ (⋃ K ∈ NetF, BadOf K)).toReal ≤ (∑ K ∈ NetF, μ (BadOf K)).toReal :=
        ENNReal.toReal_mono hSn hBunion
      _ = ∑ K ∈ NetF, (μ (BadOf K)).toReal := by
        exact ENNReal.toReal_sum (fun K hK => measure_ne_top μ (BadOf K))
      _ ≤ (NetF.card : ℝ) * EXP := hsum
  have htoRealBad : (μ Bad).toReal ≤ (NetF.card : ℝ) * EXP := by
    have hle : μ Bad ≤ μ (⋃ K ∈ NetF, BadOf K) := by
      calc
        μ Bad ≤ μ (⋃ K ∈ NetF, BadOf K) + μ Out := by
          change μ ((⋃ K ∈ NetF, BadOf K) ∪ Out) ≤ μ (⋃ K ∈ NetF, BadOf K) + μ Out
          exact measure_union_le _ _
        _ = μ (⋃ K ∈ NetF, BadOf K) := by rw [hOut, add_zero]
    have hne : μ (⋃ K ∈ NetF, BadOf K) ≠ ⊤ := measure_ne_top μ _
    calc
      (μ Bad).toReal ≤ (μ (⋃ K ∈ NetF, BadOf K)).toReal := ENNReal.toReal_mono hne hle
      _ ≤ (NetF.card : ℝ) * EXP := htoRealUnion
  have hδR : 0 < (δ : ℝ) := by exact_mod_cast hδpos
  have hraw_le : (δ : ℝ) ^ (-netGeomConstantMRaw E) ≤ (δ : ℝ) ^ (-(netGeomConstantM E)) := by
    exact Real.rpow_le_rpow_of_exponent_ge hδR hδ1 (by linarith [netGeomConstantM_gt_raw (E := E)])
  have hNetF_card' : (NetF.card : ℝ) ≤ netGeomConstantC E * (δ : ℝ) ^ (-(netGeomConstantM E)) := by
    calc
      (NetF.card : ℝ) ≤ netGeomConstantC E * (δ : ℝ) ^ (-netGeomConstantMRaw E) := hNetF_card
      _ ≤ netGeomConstantC E * (δ : ℝ) ^ (-(netGeomConstantM E)) := by
        exact mul_le_mul_of_nonneg_left hraw_le (netGeomConstantC_pos E).le
  have hbelow : (NetF.card : ℝ) * EXP < 1 / 10 := by
    have hmono : (NetF.card : ℝ) * EXP ≤
        (netGeomConstantC E * (δ : ℝ) ^ (-(netGeomConstantM E))) * EXP :=
      mul_le_mul_of_nonneg_right hNetF_card' (Real.exp_pos _).le
    have hU : (netGeomConstantC E * (δ : ℝ) ^ (-(netGeomConstantM E))) * EXP < 1 / 10 := by
      simpa [EXP, L] using
        (net_union_bound_lt (M := 1) (A := edNetCalibration E) one_pos le_rfl hδpos hδ1)
    exact lt_of_le_of_lt hmono hU
  have h1_10 : (μ Bad).toReal < 1 / 10 := lt_of_le_of_lt htoRealBad hbelow
  have h1_4 : (μ Bad).toReal < 1 / 4 := lt_trans h1_10 (by norm_num)
  have hBad_lt : μ Bad < ENNReal.ofReal (1 / 4) := by
    rw [ENNReal.lt_ofReal_iff_toReal_lt (measure_ne_top μ Bad)]
    exact h1_4
  have hFrostBad_lt : μ FrostBad < ENNReal.ofReal (1 / 4) := by
    exact lt_of_le_of_lt (measure_mono hcontain) hBad_lt
  simpa [μ, FrostBad] using hFrostBad_lt

end

end Kakeya

end

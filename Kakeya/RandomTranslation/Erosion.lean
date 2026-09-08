/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Thickness.Volume

/-!
# Volume bounds for feasible tube translations

This file bounds the volume of translation vectors in a ball for which a
unit-length set remains inside a convex body. It is the geometric input for
the random-translation probability estimate.
-/

@[expose] public section

open MeasureTheory Metric

namespace Kakeya

variable
  {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/-- Constant in `Convex.volume_le_of_subset_closedBall_of_one_le_dist` and
`Convex.volume_erosion_inter_closedBall_le`.  It depends only on the ambient dimension `n`:
`2 ^ (n + 1)` from the two-sided volume/width comparison, divided by the inscribed-simplex
constant `1 / n!`. -/
@[nolint defsWithUnderscore]
noncomputable def translationErosionVolumeConstant (n : ℕ) : NNReal :=
  2 ^ (n + 1) / lt_volume_convexHull.c n

theorem translationErosionVolumeConstant_pos (n : ℕ) : 0 < translationErosionVolumeConstant n := by
  unfold translationErosionVolumeConstant
  positivity

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
/-- A set containing two points at distance at least `1` has rank-`0` `ethickness` at least `1/2`.

A rank-`0` affine subspace is a single point (or empty), so a `cthickening` of one containing the
set is a closed ball; a ball containing both points has radius at least half their distance. -/
private theorem one_le_two_mul_ethickness_zero {K : Set E} {x y : E}
    (hx : x ∈ K) (hy : y ∈ K) (hxy : 1 ≤ dist x y) :
    1 ≤ 2 * ethickness ℝ K 0 := by
  rw [le_mul_ethickness_iff K 0 (1 : ENNReal) (C := 2) (by norm_num) (by norm_num)]
  intro r' A hA hKct
  have hA_nonempty : (A : Set E).Nonempty := by
    have hx' : x ∈ cthickening (r' : ℝ) (A : Set E) := hKct hx
    by_contra! hAempty
    rw [hAempty, Metric.cthickening_empty] at hx'
    exact hx'
  obtain ⟨p, hp⟩ := hA_nonempty
  have h_dir_eq_bot : A.direction = ⊥ := by
    have h_rank_eq_zero : Module.rank ℝ A.direction = 0 := le_antisymm hA zero_le
    exact ((Submodule.rank_eq_zero (S := A.direction)).mp h_rank_eq_zero)
  have hA_sub_singleton : (A : Set E) ⊆ {p} := by
    intro q hq
    have h_vsub_mem : q -ᵥ p ∈ A.direction := AffineSubspace.vsub_mem_direction hq hp
    rw [h_dir_eq_bot, Submodule.mem_bot] at h_vsub_mem
    have h_eq : q = p := eq_of_vsub_eq_zero h_vsub_mem
    exact Set.mem_singleton_iff.mpr h_eq
  have hK_sub_ball : K ⊆ closedBall p (r' : ℝ) := by
    calc
      K ⊆ cthickening (r' : ℝ) (A : Set E) := hKct
      _ ⊆ cthickening (r' : ℝ) ({p} : Set E) :=
        Metric.cthickening_subset_of_subset (r' : ℝ) hA_sub_singleton
      _ = closedBall p (r' : ℝ) := Metric.cthickening_singleton p (by exact r'.2)
  have hx_ball : x ∈ closedBall p (r' : ℝ) := hK_sub_ball hx
  have hy_ball : y ∈ closedBall p (r' : ℝ) := hK_sub_ball hy
  have hdist_xp : dist x p ≤ (r' : ℝ) := hx_ball
  have hdist_yp : dist y p ≤ (r' : ℝ) := hy_ball
  have hdist_py : dist p y ≤ (r' : ℝ) := by rw [dist_comm]; exact hdist_yp
  have hdist_xy : dist x y ≤ 2 * (r' : ℝ) :=
    calc
      dist x y ≤ dist x p + dist p y := dist_triangle _ _ _
      _ ≤ (r' : ℝ) + (r' : ℝ) := add_le_add hdist_xp hdist_py
      _ = 2 * (r' : ℝ) := by ring
  have h_one_le_two_r' : (1 : ℝ) ≤ 2 * (r' : ℝ) := hxy.trans hdist_xy
  have h_nn : (1 : NNReal) ≤ 2 * r' := by exact_mod_cast h_one_le_two_r'
  have h_enn : (1 : ENNReal) ≤ (2 : ENNReal) * (r' : ENNReal) := by
    calc
      (1 : ENNReal) = ((1 : NNReal) : ENNReal) := by norm_num
      _ ≤ ((2 * r' : NNReal) : ENNReal) := ENNReal.coe_le_coe.mpr h_nn
      _ = ((2 : NNReal) : ENNReal) * ((r' : NNReal) : ENNReal) := by simp [ENNReal.coe_mul]
      _ = (2 : ENNReal) * (r' : ENNReal) := by norm_num
  exact h_enn

/-- **Ball-versus-length volume comparison.**

If a subset `V` of a convex set `K` is contained in a ball of radius `r`, and `K` contains two
points at distance at least `1`, then `volume V ≤ C_n · r · volume K`.

The mechanism is a width-product comparison rather than any integration: `V ⊆ K` gives
`ethickness V i ≤ ethickness K i` at every rank, while `V ⊆ closedBall v₀ r` gives the much
better `ethickness V 0 ≤ r`; and `ethickness K 0 ≥ 1/2`, because a rank-`0` affine subspace is a
single point and `K` contains two points at distance `1`.  So the rank-`0` factor alone gains the
factor `2 r`, and the two-sided comparison `volume_le_prod_ethickness` /
`Convex.ethickness_prod_le_volume` turns that into the stated volume bound.

This is the geometric input behind the sharp per-tube translation probability: a unit-length tube
can only be translated into `K` by vectors confined to a ball of radius `r`, which is a factor `r`
smaller than the crude `volume K` bound. -/
private theorem Convex.volume_le_of_subset_closedBall_of_one_le_dist
    {V K : Set E} (hK : Convex ℝ K) (hVK : V ⊆ K)
    {v₀ : E} {r : NNReal} (hVball : V ⊆ Metric.closedBall v₀ r)
    {x y : E} (hx : x ∈ K) (hy : y ∈ K) (hxy : 1 ≤ dist x y) :
    volume V ≤ translationErosionVolumeConstant (Module.finrank ℝ E) * r * volume K := by
  set n := Module.finrank ℝ E with hn_def
  have hn_pos : 0 < n := Module.finrank_pos
  have hn0 : (0 : ℕ) ∈ Finset.range n := Finset.mem_range.mpr (by omega)
  -- Step 1: volume V ≤ 2^n * ∏_{i∈range n} ethickness ℝ V i
  have hV0 : volume V ≤ (2 : ENNReal) ^ n * ∏ i ∈ Finset.range n, ethickness ℝ V i := by
    calc
      volume V ≤ (2 : ENNReal) ^ (Module.finrank ℝ E) *
          ∏ i ∈ Finset.range (Module.finrank ℝ E), ethickness ℝ V i := volume_le_prod_ethickness V
      _ = (2 : ENNReal) ^ n * ∏ i ∈ Finset.range n, ethickness ℝ V i := by simp [hn_def]
  -- Step 2: split product at i = 0
  have hprod_split : ∏ i ∈ Finset.range n, ethickness ℝ V i =
      ethickness ℝ V 0 * ∏ i ∈ (Finset.range n).erase 0, ethickness ℝ V i := by
    rw [← Finset.prod_erase_mul (Finset.range n) (ethickness ℝ V) hn0, mul_comm]
  -- Step 3: bound individual factors
  have h_ethick0 : ethickness ℝ V 0 ≤ (r : ENNReal) :=
    ethickness_le_of_subset_closedBall r hVball 0
  have h_ethicki (i : ℕ) (hi : i ∈ (Finset.range n).erase 0) :
      ethickness ℝ V i ≤ ethickness ℝ K i :=
    ethickness_monotone hVK i
  have h_prod_tail :
      ∏ i ∈ (Finset.range n).erase 0, ethickness ℝ V i ≤
      ∏ i ∈ (Finset.range n).erase 0, ethickness ℝ K i :=
    Finset.prod_le_prod' (fun i hi => h_ethicki i hi)
  have h_prod_V : ∏ i ∈ Finset.range n, ethickness ℝ V i ≤ (r : ENNReal) *
      ∏ i ∈ (Finset.range n).erase 0, ethickness ℝ K i := by
    calc
      ∏ i ∈ Finset.range n, ethickness ℝ V i
          = ethickness ℝ V 0 * ∏ i ∈ (Finset.range n).erase 0, ethickness ℝ V i := hprod_split
      _ ≤ (r : ENNReal) * ∏ i ∈ (Finset.range n).erase 0, ethickness ℝ V i :=
        mul_le_mul' h_ethick0 le_rfl
      _ ≤ (r : ENNReal) * ∏ i ∈ (Finset.range n).erase 0, ethickness ℝ K i :=
        mul_le_mul' le_rfl h_prod_tail
  -- Step 4: introduce ethickness K 0 factor using one_le_two_mul_ethickness_zero
  have h_one_le_two_ethK0 : (1 : ENNReal) ≤ 2 * ethickness ℝ K 0 :=
    one_le_two_mul_ethickness_zero hx hy hxy
  have h_one_prod_tail' : ∏ i ∈ (Finset.range n).erase 0, ethickness ℝ K i ≤
      (2 * ethickness ℝ K 0) * ∏ i ∈ (Finset.range n).erase 0, ethickness ℝ K i := by
    calc
      ∏ i ∈ (Finset.range n).erase 0, ethickness ℝ K i
          = (1 : ENNReal) * ∏ i ∈ (Finset.range n).erase 0, ethickness ℝ K i := by simp
      _ ≤ (2 * ethickness ℝ K 0) * ∏ i ∈ (Finset.range n).erase 0, ethickness ℝ K i :=
        mul_le_mul' h_one_le_two_ethK0 le_rfl
  have h_prod_K_tail_eq : (2 * ethickness ℝ K 0) * ∏ i ∈ (Finset.range n).erase 0, ethickness ℝ K i
      = 2 * ∏ i ∈ Finset.range n, ethickness ℝ K i := by
    have hK_prod_eq : ethickness ℝ K 0 * ∏ i ∈ (Finset.range n).erase 0, ethickness ℝ K i =
        ∏ i ∈ Finset.range n, ethickness ℝ K i := by
      rw [← Finset.prod_erase_mul (Finset.range n) (ethickness ℝ K) hn0, mul_comm]
    calc
      (2 * ethickness ℝ K 0) * ∏ i ∈ (Finset.range n).erase 0, ethickness ℝ K i
          = 2 * (ethickness ℝ K 0 * ∏ i ∈ (Finset.range n).erase 0, ethickness ℝ K i) := by
        simp [mul_assoc]
      _ = 2 * ∏ i ∈ Finset.range n, ethickness ℝ K i := by rw [hK_prod_eq]
  have h_prod_V_total : ∏ i ∈ Finset.range n, ethickness ℝ V i ≤
      2 * (r : ENNReal) * ∏ i ∈ Finset.range n, ethickness ℝ K i := by
    calc
      ∏ i ∈ Finset.range n, ethickness ℝ V i
          ≤ (r : ENNReal) * ∏ i ∈ (Finset.range n).erase 0, ethickness ℝ K i := h_prod_V
      _ ≤ (r : ENNReal) * ((2 * ethickness ℝ K 0) *
          ∏ i ∈ (Finset.range n).erase 0, ethickness ℝ K i) :=
        mul_le_mul' le_rfl h_one_prod_tail'
      _ = (r : ENNReal) * (2 * ∏ i ∈ Finset.range n, ethickness ℝ K i) := by
        rw [h_prod_K_tail_eq]
      _ = 2 * (r : ENNReal) * ∏ i ∈ Finset.range n, ethickness ℝ K i := by ring
  -- Step 5: from ethickness_prod_le_volume, get ∏ ethickness K i ≤ (c n)⁻¹ * volume K
  have hc_pos : lt_volume_convexHull.c n > 0 := lt_volume_convexHull.c_pos n
  have hc_ne_zero : (lt_volume_convexHull.c n : ENNReal) ≠ 0 := by exact_mod_cast hc_pos.ne'
  have hc_ne_top : (lt_volume_convexHull.c n : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hKprod_le_vol : (lt_volume_convexHull.c n : ENNReal) *
      ∏ i ∈ Finset.range n, ethickness ℝ K i ≤ volume K := hK.ethickness_prod_le_volume
  have h_prod_K_le_inv_vol : ∏ i ∈ Finset.range n, ethickness ℝ K i ≤
      ((lt_volume_convexHull.c n : ENNReal))⁻¹ * volume K := by
    calc
      ∏ i ∈ Finset.range n, ethickness ℝ K i
          = (1 : ENNReal) * ∏ i ∈ Finset.range n, ethickness ℝ K i := by simp
      _ = (((lt_volume_convexHull.c n : ENNReal))⁻¹ * (lt_volume_convexHull.c n : ENNReal)) *
          ∏ i ∈ Finset.range n, ethickness ℝ K i := by
        simp [hc_ne_zero, hc_ne_top, ENNReal.inv_mul_cancel]
      _ = ((lt_volume_convexHull.c n : ENNReal))⁻¹ *
          ((lt_volume_convexHull.c n : ENNReal) * ∏ i ∈ Finset.range n, ethickness ℝ K i) := by
        simp [mul_assoc]
      _ ≤ ((lt_volume_convexHull.c n : ENNReal))⁻¹ * volume K :=
        mul_le_mul' le_rfl hKprod_le_vol
  -- Step 6: assemble
  have h_volV : volume V ≤ (2 : ENNReal) ^ (n + 1) * ((lt_volume_convexHull.c n : ENNReal))⁻¹ *
      (r : ENNReal) * volume K := by
    calc
      volume V ≤ (2 : ENNReal) ^ n * ∏ i ∈ Finset.range n, ethickness ℝ V i := hV0
      _ ≤ (2 : ENNReal) ^ n * (2 * (r : ENNReal) * ∏ i ∈ Finset.range n, ethickness ℝ K i) :=
        mul_le_mul' le_rfl h_prod_V_total
      _ = (2 : ENNReal) ^ n * 2 * (r : ENNReal) * ∏ i ∈ Finset.range n, ethickness ℝ K i := by
        simp [mul_assoc]
      _ = (2 : ENNReal) ^ (n + 1) * (r : ENNReal) * ∏ i ∈ Finset.range n, ethickness ℝ K i := by
        simp [pow_succ, mul_comm, mul_left_comm]
      _ ≤ (2 : ENNReal) ^ (n + 1) * (r : ENNReal) *
          (((lt_volume_convexHull.c n : ENNReal))⁻¹ * volume K) :=
        mul_le_mul' le_rfl h_prod_K_le_inv_vol
      _ = (2 : ENNReal) ^ (n + 1) * ((lt_volume_convexHull.c n : ENNReal))⁻¹ *
          (r : ENNReal) * volume K := by
        simp [mul_assoc, mul_comm, mul_left_comm]
  -- Step 7: identify the constant
  have hC_coe : (translationErosionVolumeConstant n : ENNReal) =
      (2 : ENNReal) ^ (n + 1) * ((lt_volume_convexHull.c n : ENNReal))⁻¹ := by
    dsimp [translationErosionVolumeConstant]
    rw [ENNReal.coe_div (lt_volume_convexHull.c_pos n).ne', ENNReal.coe_pow, ENNReal.coe_ofNat]
    rw [div_eq_mul_inv]
  calc
    volume V ≤ (2 : ENNReal) ^ (n + 1) * ((lt_volume_convexHull.c n : ENNReal))⁻¹ *
          (r : ENNReal) * volume K := h_volV
    _ = (translationErosionVolumeConstant n : ENNReal) * (r : ENNReal) * volume K := by
      rw [hC_coe]
    _ = translationErosionVolumeConstant (Module.finrank ℝ E) * r * volume K := by
      simp [hn_def]

/-- **Erosion bound (Brick X).**

Let `K` be convex and let `S` be any set containing two points `x`, `y` at distance at least `1`
(the intended case: `S` is a `δ`-tube and `x`, `y` are the endpoints of its unit core segment).
Then the set of translation vectors `v` lying in a ball of radius `r` for which the translate
`v + S` still fits inside `K` has volume at most `C_n · r · volume K`.

Compared with the trivial bound `volume K` this saves a factor `r`, and that saving is exactly
what makes the random-translation density estimate independent of the number of translations. -/
theorem Convex.volume_erosion_inter_closedBall_le
    {K S : Set E} (hK : Convex ℝ K)
    {x y : E} (hx : x ∈ S) (hy : y ∈ S) (hxy : 1 ≤ dist x y)
    (v₀ : E) (r : NNReal) :
    volume ({v : E | (fun z => v + z) '' S ⊆ K} ∩ Metric.closedBall v₀ r)
      ≤ translationErosionVolumeConstant (Module.finrank ℝ E) * r * volume K := by
  set Er := {v : E | (fun z => v + z) '' S ⊆ K} with hEr_def
  set V := Er ∩ Metric.closedBall v₀ r with hV_def
  by_cases hV_empty : V = ∅
  · rw [hV_empty]
    simp
  have hV_nonempty : V.Nonempty := Set.nonempty_iff_ne_empty.mpr hV_empty
  rcases hV_nonempty with ⟨v, hv⟩
  rcases hv with ⟨hvEr, hvBall⟩
  set K' := (fun z : E => z - x) '' K with hK'_def
  have hK'_convex : Convex ℝ K' := by
    -- hK.translate (-x) gives Convex ℝ ((x + ·)⁻¹' K) via Set.image_add_left as a simp lemma
    -- we need K' = (fun z => z - x) '' K = ((-x) + ·) '' K = (x + ·)⁻¹' K
    -- so we use ← Set.image_add_left to rewrite back
    simpa [K', sub_eq_add_neg, add_comm, Set.image_add_left] using hK.translate (-x)
  have hVK' : V ⊆ K' := by
    intro w hw
    rw [hV_def] at hw
    rcases hw with ⟨hwEr, hwBall⟩
    rw [hEr_def] at hwEr
    have hwSK : (fun z => w + z) '' S ⊆ K := hwEr
    have hwxK : w + x ∈ K := hwSK (Set.mem_image_of_mem (fun z => w + z) hx)
    have : w = (w + x) - x := by simp
    rw [this]
    exact Set.mem_image_of_mem (fun z => z - x) hwxK
  have hVball : V ⊆ Metric.closedBall v₀ r := Set.inter_subset_right
  have hvolK'_eq : volume K' = volume K := by
    calc
      volume K' = volume ((x + ·) ⁻¹' K) := by
        simp [K', sub_eq_add_neg]
      _ = volume K := by rw [measure_preimage_add volume x K]
  have hvxK : v + x ∈ K := by
    have h_image : (fun z => v + z) '' S ⊆ K := hvEr
    exact h_image (Set.mem_image_of_mem (fun z => v + z) hx)
  have hvyK : v + y ∈ K := by
    have h_image : (fun z => v + z) '' S ⊆ K := hvEr
    exact h_image (Set.mem_image_of_mem (fun z => v + z) hy)
  have hvK' : v ∈ K' := by
    have : v = (v + x) - x := by simp
    rw [this]
    exact Set.mem_image_of_mem (fun z => z - x) hvxK
  have hvy_xK' : (v + y) - x ∈ K' :=
    Set.mem_image_of_mem (fun z => z - x) hvyK
  have hdist_eq : dist v ((v + y) - x) = dist x y := by
    rw [dist_eq_norm, dist_eq_norm]
    have : v - ((v + y) - x) = x - y := by abel
    rw [this]
  have hdist_ge_one : 1 ≤ dist v ((v + y) - x) := hxy.trans_eq hdist_eq.symm
  calc
    volume V ≤ translationErosionVolumeConstant (Module.finrank ℝ E) * r * volume K' :=
      Convex.volume_le_of_subset_closedBall_of_one_le_dist hK'_convex hVK' hVball
        hvK' hvy_xK' hdist_ge_one
    _ = translationErosionVolumeConstant (Module.finrank ℝ E) * r * volume K := by rw [hvolK'_eq]

end Kakeya

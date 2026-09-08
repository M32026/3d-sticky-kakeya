/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Conjunct6EssDistinct
public import Kakeya.Tube.Nets

/-!
# The anchored `ρ`-net: one scale of the loose hierarchy, at the existing constants

The loose-hierarchy condition associated with
`Kakeya.VeryNotSticky.SideDataObligations` as *"produce a
`Kakeya.LooseUniform.LooseShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) 4 …"*,
because everything inside that binder is already the compiled theorem
`Kakeya.VeryNotSticky.exists_Cang_angularFibre_le_of_looseUniform`. What remains is the
**producer**, and its keystone is one scale:

> a finite family of `ρ`-tubes, and an assignment of every `δ`-tube of the family (`4δ ≤ ρ`,
> carrier in the unit ball) to one of them, such that
> * the member lies in the **`4`-dilate** of its node
>   (`Kakeya.LooseUniform.LooseGridCoverSystem.le_dilate_tube_assign` at `K = 4`),
> * its direction is within **`ρ/4`** of the node's
>   (`Kakeya.LooseUniform.LooseGridCoverSystem.dir_close_tube_assign`),
> * the node map is injective on the used index set
>   (`Kakeya.LooseUniform.LooseUniformTubeSet.tube_injOn`), and
> * for **every** `ρ`-tube `V`, at most an absolute constant many used nodes have a member in
>   `Kakeya.Tube.dilate V 8`
>   (`Kakeya.LooseUniform.LooseUniformTubeSet.boundedOverlapDil` at `K + 4 = 8`).

`Kakeya.LooseUniform.exists_anchorCover` is exactly that, **at the existing constants `K = 4`
and `ρ/4`** — no field is weakened.

## Why the net is anchored, and why that is the whole point

The obvious candidate, `Tube.grid_net_tight`, already gives the first two clauses (it covers a
`δ`-tube by a `ρ`-tube *exactly*, with midpoint within `ρ/32` and direction within `ρ/16`).  It
does **not** give the fourth: its nodes are separated in the **midpoint**, so a node may be
translated **along its own axis** by `ρ/64` and still count as a new node, and
`Kakeya.Tube.dilate V 8` is `8` times as long as a node — so `Θ(1/ρ)` distinct net tubes have a
member inside one `8`-dilate, and no `δ`-free bound exists.   identified the
repair and left it uncompiled; this file compiles it.

The repair is to bin a member not by its midpoint but by its **anchor**
`Kakeya.LooseUniform.anchorAt`, the component of its centre orthogonal to the chosen node
direction.  The anchor kills the axial degree of freedom, and
`Kakeya.LooseUniform.anchor_near_axisFoot` is the estimate that makes it work: a member inside
`Kakeya.Tube.dilate V 8` has its anchor within `82 ρ` of `Kakeya.LooseUniform.axisFoot V`, a
point depending on `V` **alone** — the `|t| ≤ 4` axial freedom of the dilate cancels against the
anchor's own subtraction.  Bounded overlap is then the packing bound
`Tube.card_le_of_L1_separated_in_box` in the four net coordinates, with the absolute constant
`Kakeya.LooseUniform.anchorOverlapConst = 2 · 21249 ^ 6`.

## What this file does NOT do

It is **one scale**.  A `Kakeya.LooseUniform.LooseGridCoverSystem` additionally needs the levels
`0 … N` to be `nested`, and `Kakeya.LooseUniform.LooseUniformTubeSet` needs GWZ Definition
2.1(iii)'s two-sided class bracket, which costs a refinement (the pruning engine
`Tube.exists_pruned_subset_noroot_notop`).  **Nothing here discharges conjunct 6**, and nothing
here may be cited as doing so.
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped NNReal RealInnerProductSpace

namespace Kakeya
namespace LooseUniform

noncomputable def axisFoot {ρ : NNReal} (V : Tube ρ E3) : E3 :=
  V.center - ⟪V.center, V.direction⟫ • V.direction

noncomputable def anchorAt {δ : NNReal} (T : Tube δ E3) (d : E3) : E3 :=
  T.center - ⟪T.center, d⟫ • d

theorem center_mem_carrier {δ : NNReal} (hδ : 0 < δ) (T : Tube δ E3) :
    T.center ∈ T.carrier := by
  have h := Tube.midpoint_mem_carrier hδ T
  have he : T.center = T.midpoint := by
    change midpoint ℝ T.x T.y = _
    rw [midpoint_eq_smul_add]; norm_num
  rwa [he]

private theorem anchor_algebra (c v fv uv ev : E3) (A t' c₀ : ℝ)
    (hc : c = v + t' • uv + fv)
    (hA : A = c₀ + t' + ⟪fv, uv⟫ + ⟪c, ev⟫) :
    (c - A • (uv + ev)) - (v - c₀ • uv)
      = (-(⟪fv, uv⟫ + ⟪c, ev⟫)) • uv + fv - A • ev := by
  rw [hA, hc]
  module

theorem anchor_near_axisFoot {δ ρ : NNReal}
    (T : Tube δ E3) (V : Tube ρ E3) {d : E3} (hd : ‖d‖ = 1)
    (hm1 : ‖T.center‖ ≤ 1) (hδ : 0 < δ)
    (hdT : ‖T.direction - d‖ ≤ (ρ : ℝ) / 4)
    (hTV : T.toConvexSpaceBody ≤ Kakeya.Tube.dilate V 8) :
    ∃ σ : ℝ, |σ| = 1 ∧ ‖d - σ • V.direction‖ ≤ 33 * (ρ : ℝ) ∧
      ‖anchorAt T d - axisFoot V‖ ≤ 82 * (ρ : ℝ) := by
  have hρ0 : (0 : ℝ) ≤ (ρ : ℝ) := ρ.coe_nonneg
  obtain ⟨σ₁, hσ₁, hdir₁⟩ :=
    Kakeya.VeryNotSticky.exists_sign_norm_direction_sub_le_of_le_dilate T V
      (by norm_num : (0:ℝ) < 8) hTV
  have hσsq : σ₁ * σ₁ = 1 := by
    rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp hσ₁ with h | h <;> rw [h] <;> norm_num
  have hVdirnorm : ‖V.direction‖ = 1 := Tube.norm_direction V
  -- the reference unit vector
  have hu : ‖σ₁ • V.direction‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, hσ₁, hVdirnorm, one_mul]
  have hVback : σ₁ • (σ₁ • V.direction) = V.direction := by
    rw [smul_smul, hσsq, one_smul]
  have he33 : ‖d - σ₁ • V.direction‖ ≤ 33 * (ρ : ℝ) := by
    calc ‖d - σ₁ • V.direction‖
        ≤ ‖d - T.direction‖ + ‖T.direction - σ₁ • V.direction‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ (ρ : ℝ) / 4 + 4 * 8 * (ρ : ℝ) := by
            refine add_le_add ?_ hdir₁
            rw [← norm_neg]
            simpa using hdT
      _ ≤ 33 * (ρ : ℝ) := by linarith
  refine ⟨σ₁, hσ₁, he33, ?_⟩
  -- position
  obtain ⟨t, ht, hdist⟩ :=
    exists_axis_point_of_mem_dilate V (by norm_num : (0:ℝ) < 8)
      (hTV (center_mem_carrier hδ T))
  have hf : ‖T.center - (V.center + t • V.direction)‖ ≤ 8 * (ρ : ℝ) := by
    rw [← dist_eq_norm]; exact hdist
  have htv : t • V.direction = (t * σ₁) • (σ₁ • V.direction) := by
    rw [smul_smul, mul_assoc, hσsq, mul_one]
  have hcenter : T.center
      = V.center + (t * σ₁) • (σ₁ • V.direction)
        + (T.center - (V.center + t • V.direction)) := by
    rw [← htv]; module
  have hfoot : axisFoot V = V.center - ⟪V.center, σ₁ • V.direction⟫ • (σ₁ • V.direction) := by
    rw [axisFoot, real_inner_smul_right, smul_smul,
      mul_comm σ₁ (⟪V.center, V.direction⟫ : ℝ), mul_assoc, hσsq, mul_one]
  have hdsplit : d = (σ₁ • V.direction) + (d - σ₁ • V.direction) := by module
  have hA : ⟪T.center, d⟫
      = ⟪V.center, σ₁ • V.direction⟫ + (t * σ₁)
        + ⟪T.center - (V.center + t • V.direction), σ₁ • V.direction⟫
        + ⟪T.center, d - σ₁ • V.direction⟫ := by
    nth_rewrite 1 [hdsplit]
    rw [inner_add_right]
    nth_rewrite 1 [hcenter]
    rw [inner_add_left, inner_add_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq]
    rw [hu]
    ring
  have hkey := anchor_algebra T.center V.center
    (T.center - (V.center + t • V.direction)) (σ₁ • V.direction) (d - σ₁ • V.direction)
    ⟪T.center, d⟫ (t * σ₁) ⟪V.center, σ₁ • V.direction⟫ hcenter hA
  have hgoal : anchorAt T d - axisFoot V
      = (-(⟪T.center - (V.center + t • V.direction), σ₁ • V.direction⟫
            + ⟪T.center, d - σ₁ • V.direction⟫)) • (σ₁ • V.direction)
        + (T.center - (V.center + t • V.direction))
        - ⟪T.center, d⟫ • (d - σ₁ • V.direction) := by
    rw [anchorAt, hfoot, ← hkey, ← hdsplit]
  rw [hgoal]
  have hb1 : |⟪T.center - (V.center + t • V.direction), σ₁ • V.direction⟫| ≤ 8 * (ρ : ℝ) := by
    calc |⟪T.center - (V.center + t • V.direction), σ₁ • V.direction⟫|
        ≤ ‖T.center - (V.center + t • V.direction)‖ * ‖σ₁ • V.direction‖ :=
          abs_real_inner_le_norm _ _
      _ ≤ 8 * (ρ : ℝ) := by rw [hu, mul_one]; exact hf
  have hb2 : |⟪T.center, d - σ₁ • V.direction⟫| ≤ 33 * (ρ : ℝ) := by
    calc |⟪T.center, d - σ₁ • V.direction⟫|
        ≤ ‖T.center‖ * ‖d - σ₁ • V.direction‖ := abs_real_inner_le_norm _ _
      _ ≤ 1 * (33 * (ρ : ℝ)) := by
            refine mul_le_mul hm1 he33 (norm_nonneg _) (by norm_num)
      _ = 33 * (ρ : ℝ) := one_mul _
  have hb3 : |⟪T.center, d⟫| ≤ 1 := by
    calc |⟪T.center, d⟫| ≤ ‖T.center‖ * ‖d‖ := abs_real_inner_le_norm _ _
      _ ≤ 1 * 1 := mul_le_mul hm1 (le_of_eq hd) (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  calc ‖(-(⟪T.center - (V.center + t • V.direction), σ₁ • V.direction⟫
            + ⟪T.center, d - σ₁ • V.direction⟫)) • (σ₁ • V.direction)
        + (T.center - (V.center + t • V.direction))
        - ⟪T.center, d⟫ • (d - σ₁ • V.direction)‖
      ≤ ‖(-(⟪T.center - (V.center + t • V.direction), σ₁ • V.direction⟫
            + ⟪T.center, d - σ₁ • V.direction⟫)) • (σ₁ • V.direction)
          + (T.center - (V.center + t • V.direction))‖
        + ‖⟪T.center, d⟫ • (d - σ₁ • V.direction)‖ := norm_sub_le _ _
    _ ≤ (‖(-(⟪T.center - (V.center + t • V.direction), σ₁ • V.direction⟫
            + ⟪T.center, d - σ₁ • V.direction⟫)) • (σ₁ • V.direction)‖
          + ‖T.center - (V.center + t • V.direction)‖)
        + ‖⟪T.center, d⟫ • (d - σ₁ • V.direction)‖ := by
          gcongr; exact norm_add_le _ _
    _ ≤ ((8 * (ρ:ℝ) + 33 * (ρ:ℝ)) + 8 * (ρ:ℝ)) + 33 * (ρ:ℝ) := by
          gcongr
          · rw [norm_smul, hu, mul_one, Real.norm_eq_abs, abs_neg]
            exact (abs_add_le _ _).trans (add_le_add hb1 hb2)
          · rw [norm_smul, Real.norm_eq_abs]
            calc |⟪T.center, d⟫| * ‖d - σ₁ • V.direction‖
                ≤ 1 * (33 * (ρ : ℝ)) :=
                  mul_le_mul hb3 he33 (norm_nonneg _) (by norm_num)
              _ = 33 * (ρ : ℝ) := one_mul _
    _ = 82 * (ρ : ℝ) := by ring

/-- The absolute bounded-overlap constant of the anchored net. -/
def anchorOverlapConst : ℕ := 2 * 21249 ^ 6

open scoped Classical in
theorem exists_anchorCover {ι : Type*} {δ ρ : NNReal} (hδ : 0 < δ)
    (hρ1 : (ρ : ℝ) ≤ 1) (hδρ : 4 * (δ : ℝ) ≤ (ρ : ℝ))
    (s : Finset ι) (T : ι → Tube δ E3)
    (hB : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E3) 1) :
    ∃ (J : Finset ι) (a : ι → ι) (W : ι → Tube ρ E3),
      (∀ i ∈ s, a i ∈ J) ∧
      (∀ i ∈ s, a i ∈ s) ∧
      (∀ i ∈ s, (T i).toConvexSpaceBody ≤ Kakeya.Tube.dilate (W (a i)) 4) ∧
      (∀ i ∈ s, ∃ σ : ℝ, |σ| = 1 ∧
          ‖(T i).direction - σ • (W (a i)).direction‖ ≤ (ρ : ℝ) / 4) ∧
      Set.InjOn W (J : Set ι) ∧
      (∀ V : Tube ρ E3,
        (J.filter (fun j => ∃ i ∈ s, a i = j ∧
          (T i).toConvexSpaceBody ≤ Kakeya.Tube.dilate V 8)).card ≤ anchorOverlapConst) := by
  classical
  have hδ0 : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  have hρpos : (0 : ℝ) < (ρ : ℝ) := by linarith
  obtain ⟨u₀, hu₀ne⟩ := exists_ne (0 : E3)
  have hu₀ : ‖(‖u₀‖⁻¹ • u₀ : E3)‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hu₀ne)]
  rcases s.eq_empty_or_nonempty with rfl | ⟨i₀, hi₀⟩
  · refine ⟨∅, id, fun _ => Tube.ofMidpointDirection ρ 0 _ hu₀, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [anchorOverlapConst]
  haveI : Nonempty ι := ⟨i₀⟩
  obtain ⟨D, hD_unit, hD_sep, hD_cover⟩ :=
    Tube.sphere_sep_net (E := E3) (ε := (ρ : ℝ) / 32) (by linarith) (by linarith)
  obtain ⟨Pm, hPm_loc, hPm_sep, hPm_cover⟩ :=
    Tube.midpoint_sep_net (E := E3) (ε := (ρ : ℝ) / 64) (by linarith)
  have hchoiceD : ∀ i : ι, ∃ d : E3, d ∈ D ∧ ‖(T i).direction - d‖ ≤ 2 * ((ρ : ℝ) / 32) :=
    fun i => hD_cover (T i).direction (Tube.norm_direction (T i))
  choose dirOf hdirOf_mem hdirOf_close using hchoiceD
  have hdirOf_unit : ∀ i, ‖dirOf i‖ = 1 := fun i => hD_unit _ (hdirOf_mem i)
  -- the anchor, truncated so that it always lies in the ball the midpoint net covers
  set anc : ι → E3 := fun i =>
    if ‖anchorAt (T i) (dirOf i)‖ ≤ 3 then anchorAt (T i) (dirOf i) else 0 with hanc_def
  have hanc_ball : ∀ i, anc i ∈ Metric.closedBall (0 : E3) 3 := by
    intro i
    simp only [hanc_def, Metric.mem_closedBall, dist_zero_right]
    split
    · assumption
    · simp
  have hchoiceP : ∀ i : ι, ∃ p : E3, p ∈ Pm ∧ ‖anc i - p‖ ≤ 2 * ((ρ : ℝ) / 64) :=
    fun i => hPm_cover (anc i) (hanc_ball i)
  choose posOf hposOf_mem hposOf_close using hchoiceP
  -- the centre of a member of `s` lies in the unit ball
  have hcen1 : ∀ i ∈ s, ‖(T i).center‖ ≤ 1 := by
    intro i hi
    have := hB i hi (center_mem_carrier hδ (T i))
    rwa [Metric.mem_closedBall, dist_zero_right] at this
  have hanc_eq : ∀ i ∈ s, anc i = anchorAt (T i) (dirOf i) := by
    intro i hi
    have hb : ‖anchorAt (T i) (dirOf i)‖ ≤ 3 := by
      have hinner : |(⟪(T i).center, dirOf i⟫ : ℝ)| ≤ 1 := by
        calc |(⟪(T i).center, dirOf i⟫ : ℝ)| ≤ ‖(T i).center‖ * ‖dirOf i‖ :=
              abs_real_inner_le_norm _ _
          _ ≤ 1 * 1 := mul_le_mul (hcen1 i hi) (le_of_eq (hdirOf_unit i)) (norm_nonneg _)
              (by norm_num)
          _ = 1 := by norm_num
      calc ‖anchorAt (T i) (dirOf i)‖
          ≤ ‖(T i).center‖ + ‖(⟪(T i).center, dirOf i⟫ : ℝ) • dirOf i‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := by
            refine add_le_add (hcen1 i hi) ?_
            rw [norm_smul, Real.norm_eq_abs, hdirOf_unit i, mul_one]
            exact hinner
        _ ≤ 3 := by norm_num
    simp only [hanc_def, if_pos hb]
  -- the nodes
  set W : ι → Tube ρ E3 := fun j => Tube.ofMidpointDirection ρ (posOf j) (dirOf j) (hdirOf_unit j)
    with hW_def
  have hWc : ∀ j, (W j).center = posOf j := by
    intro j
    simp [hW_def, Tube.center, Tube.ofMidpointDirection, midpoint_eq_smul_add]
    module
  have hWd : ∀ j, (W j).direction = dirOf j := by
    intro j
    simp [hW_def, Tube.direction, Tube.ofMidpointDirection]
    module
  -- the cell representative
  have hex : ∀ c : E3 × E3, ∃ j : ι,
      (∃ j' , j' ∈ s ∧ (posOf j', dirOf j') = c) → (j ∈ s ∧ (posOf j, dirOf j) = c) := by
    intro c
    by_cases h : ∃ j' , j' ∈ s ∧ (posOf j', dirOf j') = c
    · obtain ⟨j, hj, hkj⟩ := h
      exact ⟨j, fun _ => ⟨hj, hkj⟩⟩
    · exact ⟨i₀, fun hc => absurd hc h⟩
  choose cellRep hcellRep using hex
  set a : ι → ι := fun i => cellRep (posOf i, dirOf i) with ha_def
  have ha_app : ∀ i : ι, a i = cellRep (posOf i, dirOf i) := fun i => rfl
  have ha_spec : ∀ i ∈ s, a i ∈ s ∧ (posOf (a i), dirOf (a i)) = (posOf i, dirOf i) :=
    fun i hi => hcellRep (posOf i, dirOf i) ⟨i, hi, rfl⟩
  have ha_mem_s : ∀ i ∈ s, a i ∈ s := fun i hi => (ha_spec i hi).1
  have ha_pos : ∀ i ∈ s, posOf (a i) = posOf i :=
    fun i hi => congrArg Prod.fst (ha_spec i hi).2
  have ha_dir : ∀ i ∈ s, dirOf (a i) = dirOf i :=
    fun i hi => congrArg Prod.snd (ha_spec i hi).2
  have ha_idem : ∀ i ∈ s, a (a i) = a i := by
    intro i hi
    rw [ha_app (a i), ha_pos i hi, ha_dir i hi, ← ha_app i]
  set J : Finset ι := s.image a with hJ_def
  have hJ_a : ∀ j ∈ J, a j = j := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact ha_idem i hi
  refine ⟨J, a, W, fun i hi => Finset.mem_image_of_mem a hi, ha_mem_s, ?_, ?_, ?_, ?_⟩
  · -- containment in the `4`-dilate of the node
    intro i hi
    have hc : (W (a i)).center = posOf i := by rw [hWc, ha_pos i hi]
    have hd : (W (a i)).direction = dirOf i := by rw [hWd, ha_dir i hi]
    refine le_dilate_of_through_point (W (a i)) (K' := 4) (r := (ρ:ℝ)/32) (θ := (ρ:ℝ)/16)
      (by norm_num) (x := (T i).center) (s₀ := (⟪(T i).center, dirOf i⟫ : ℝ)) ?_ ?_ (T i)
      (center_mem_carrier hδ (T i)) (σ := 1) (by norm_num) ?_ ?_
    · have : |(⟪(T i).center, dirOf i⟫ : ℝ)| ≤ 1 := by
        calc |(⟪(T i).center, dirOf i⟫ : ℝ)| ≤ ‖(T i).center‖ * ‖dirOf i‖ :=
              abs_real_inner_le_norm _ _
          _ ≤ 1 * 1 := mul_le_mul (hcen1 i hi) (le_of_eq (hdirOf_unit i)) (norm_nonneg _)
              (by norm_num)
          _ = 1 := by norm_num
      linarith
    · rw [hc, hd, dist_eq_norm,
        show (T i).center - (posOf i + (⟪(T i).center, dirOf i⟫ : ℝ) • dirOf i)
            = anchorAt (T i) (dirOf i) - posOf i from by rw [anchorAt]; module,
        ← hanc_eq i hi]
      calc ‖anc i - posOf i‖ ≤ 2 * ((ρ:ℝ)/64) := hposOf_close i
        _ = (ρ:ℝ)/32 := by ring
    · rw [hd, one_smul]
      calc ‖(T i).direction - dirOf i‖ ≤ 2 * ((ρ:ℝ)/32) := hdirOf_close i
        _ = (ρ:ℝ)/16 := by ring
    · linarith
  · -- direction closeness
    intro i hi
    refine ⟨1, by norm_num, ?_⟩
    rw [hWd, ha_dir i hi, one_smul]
    calc ‖(T i).direction - dirOf i‖ ≤ 2 * ((ρ:ℝ)/32) := hdirOf_close i
      _ ≤ (ρ:ℝ)/4 := by linarith
  · -- injectivity of the node map on the used index set
    intro j hj j' hj' hWeq
    have hpj : posOf j = posOf j' := by rw [← hWc, ← hWc, hWeq]
    have hdj : dirOf j = dirOf j' := by rw [← hWd, ← hWd, hWeq]
    have haa : a j = a j' := by rw [ha_app j, ha_app j', hpj, hdj]
    rwa [hJ_a j (Finset.mem_coe.mp hj), hJ_a j' (Finset.mem_coe.mp hj')] at haa
  · -- bounded overlap against an arbitrary `ρ`-tube
    intro V
    set F := J.filter (fun j => ∃ i ∈ s, a i = j ∧
      (T i).toConvexSpaceBody ≤ Kakeya.Tube.dilate V 8) with hF_def
    have hFprop : ∀ j ∈ F, ‖posOf j - axisFoot V‖ ≤ 83 * (ρ:ℝ) ∧
        (‖dirOf j - V.direction‖ ≤ 33 * (ρ:ℝ) ∨
          ‖dirOf j - (-V.direction)‖ ≤ 33 * (ρ:ℝ)) := by
      intro j hj
      obtain ⟨hjJ, i, hi, haij, hiV⟩ := Finset.mem_filter.mp hj
      obtain ⟨σ, hσ, hdd, hfoot⟩ :=
        anchor_near_axisFoot (T i) V (hdirOf_unit i) (hcen1 i hi) hδ
          ((hdirOf_close i).trans (by linarith)) hiV
      subst haij
      refine ⟨?_, ?_⟩
      · rw [ha_pos i hi]
        have hpa : ‖posOf i - anchorAt (T i) (dirOf i)‖ ≤ (ρ:ℝ)/32 := by
          have h2 := hposOf_close i
          rw [hanc_eq i hi] at h2
          calc ‖posOf i - anchorAt (T i) (dirOf i)‖
              = ‖anchorAt (T i) (dirOf i) - posOf i‖ := by rw [← norm_neg, neg_sub]
            _ ≤ 2 * ((ρ:ℝ)/64) := h2
            _ = (ρ:ℝ)/32 := by ring
        calc ‖posOf i - axisFoot V‖
            ≤ ‖posOf i - anchorAt (T i) (dirOf i)‖
              + ‖anchorAt (T i) (dirOf i) - axisFoot V‖ :=
              norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ ≤ (ρ:ℝ)/32 + 82 * (ρ:ℝ) := add_le_add hpa hfoot
          _ ≤ 83 * (ρ:ℝ) := by linarith
      · rw [ha_dir i hi]
        rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp hσ with h | h
        · left; rw [h, one_smul] at hdd; exact hdd
        · right; rw [h] at hdd; simpa using hdd
    set Fp := F.filter (fun j => ‖dirOf j - V.direction‖ ≤ 33 * (ρ:ℝ)) with hFp_def
    set Fm := F \ Fp with hFm_def
    have hcard_bound : ∀ (G : Finset ι) (cy : E3), G ⊆ F →
        (∀ j ∈ G, ‖dirOf j - cy‖ ≤ 33 * (ρ:ℝ)) → G.card ≤ 21249 ^ 6 := by
      intro G cy hGF hGy
      have hsep : ∀ x ∈ G, ∀ y ∈ G, x ≠ y →
          (ρ:ℝ)/64 ≤ ‖posOf x - posOf y‖ + ‖dirOf x - dirOf y‖ := by
        intro x hx y hy hxy
        by_cases hp : posOf x = posOf y
        · have hdne : dirOf x ≠ dirOf y := by
            intro hd
            apply hxy
            have hax : a x = x := hJ_a x (Finset.mem_filter.mp (hGF hx)).1
            have hay : a y = y := hJ_a y (Finset.mem_filter.mp (hGF hy)).1
            have haa : a x = a y := by rw [ha_app x, ha_app y, hp, hd]
            rwa [hax, hay] at haa
          have hsd := hD_sep _ (hdirOf_mem x) _ (hdirOf_mem y) hdne
          have h0 : (0:ℝ) ≤ ‖posOf x - posOf y‖ := norm_nonneg _
          linarith
        · have hsp := hPm_sep _ (hposOf_mem x) _ (hposOf_mem y) hp
          have h0 : (0:ℝ) ≤ ‖dirOf x - dirOf y‖ := norm_nonneg _
          linarith
      have hpack := Tube.card_le_of_L1_separated_in_box (E := E3) G
        (fun j => posOf j) (fun j => dirOf j) (axisFoot V) cy
        (R := 83 * (ρ:ℝ)) (r := (ρ:ℝ)/64) (by linarith) hsep
        (fun j hj => (hFprop j (hGF hj)).1)
        (fun j hj => (hGy j hj).trans (by linarith))
      have hfr : Module.finrank ℝ E3 = 3 := by simp [E3]
      rw [hfr] at hpack
      have hval : ((83 * (ρ:ℝ) + ((ρ:ℝ)/64) / 4) / (((ρ:ℝ)/64) / 4)) = 21249 := by
        rw [div_eq_iff (by positivity)]
        ring
      rw [hval] at hpack
      exact_mod_cast hpack
    have hFp_card : Fp.card ≤ 21249 ^ 6 :=
      hcard_bound Fp V.direction (Finset.filter_subset _ _)
        (fun j hj => (Finset.mem_filter.mp hj).2)
    have hFm_card : Fm.card ≤ 21249 ^ 6 := by
      refine hcard_bound Fm (-V.direction) Finset.sdiff_subset ?_
      intro j hj
      obtain ⟨hjF, hjn⟩ := Finset.mem_sdiff.mp hj
      rcases (hFprop j hjF).2 with h | h
      · exact absurd (Finset.mem_filter.mpr ⟨hjF, h⟩) hjn
      · exact h
    have hsplit : F.card ≤ Fp.card + Fm.card := by
      have hFeq : F.card = (Fp ∪ Fm).card := by
        congr 1
        rw [hFm_def, Finset.union_sdiff_of_subset (Finset.filter_subset _ _)]
      rw [hFeq]
      exact Finset.card_union_le _ _
    calc F.card ≤ Fp.card + Fm.card := hsplit
      _ ≤ 21249 ^ 6 + 21249 ^ 6 := Nat.add_le_add hFp_card hFm_card
      _ = anchorOverlapConst := by rw [anchorOverlapConst]; ring


/-! ## The multiscale anchored cover

The one-scale construction is repeated at every grid level, and the two structural fields of
`Kakeya.LooseUniform.LooseGridCoverSystem` that relate the levels — `nested` — is obtained by a
**downward recursion on the cell key, not on a chain of members**.

That choice is the whole content of this section.  Chaining through cell *representatives*
(`i ↦ representative of `i`'s level-`(k+1)` cell ↦ …`) does not work: two members of one cell may
differ by an **axial** displacement of order `1`, and when the node direction rotates by `Θ(ρ_k)`
between levels that displacement re-enters as a `Θ(ρ_k)` *perpendicular* error at **every** one of
the `N` steps, so the containment constant would grow like `N`.  Recursing on the key instead
carries only *anchored* data: the level-`k` key is computed from the level-`(k+1)` **key**
(`Kakeya.LooseUniform.downIter`), and the axial component cancels because
`Kakeya.LooseUniform.perp d' d = Kakeya.LooseUniform.perp d' (d - d')`.  The resulting errors are
geometric in `k` and the constants are absolute — the invariant is
`‖(T i).direction - d_k‖ ≤ ρ_k/8` and `‖p_k - perp d_k (T i).center‖ ≤ 3 ρ_k/16`.

Nesting is then free (`key k` is a function of `key (k+1)`), node injectivity is free (the level-`k`
index set is the set of level-`k` **keys**, and the node is determined by the key), and the whole
construction has **retention `1`**: no member of `s` is discarded.
-/

/-- Iterate a level-indexed step map downward from level `N` to level `k`. -/
def downIter {α : Type*} (N : ℕ) (base : α) (stp : ℕ → α → α) (k : ℕ) : α :=
  if _h : k < N then stp k (downIter N base stp (k + 1)) else base
termination_by N - k
decreasing_by omega

lemma downIter_of_lt {α : Type*} (N : ℕ) (base : α) (stp : ℕ → α → α) {k : ℕ} (h : k < N) :
    downIter N base stp k = stp k (downIter N base stp (k + 1)) := by
  rw [downIter]; simp [h]

lemma downIter_of_not_lt {α : Type*} (N : ℕ) (base : α) (stp : ℕ → α → α) {k : ℕ}
    (h : ¬ k < N) : downIter N base stp k = base := by
  rw [downIter]; simp [h]

/-- The component of `v` orthogonal to the unit vector `d`. -/
noncomputable def perp (d v : E3) : E3 := v - ⟪v, d⟫ • d

lemma anchorAt_eq_perp {δ : NNReal} (T : Tube δ E3) (d : E3) :
    anchorAt T d = perp d T.center := rfl

lemma axisFoot_eq_perp {ρ : NNReal} (V : Tube ρ E3) :
    axisFoot V = perp V.direction V.center := rfl

lemma perp_sub (d v w : E3) : perp d (v - w) = perp d v - perp d w := by
  simp only [perp, inner_sub_left, sub_smul]; module

lemma perp_smul (d : E3) (t : ℝ) (v : E3) : perp d (t • v) = t • perp d v := by
  simp only [perp, real_inner_smul_left, smul_smul, smul_sub]

lemma perp_self {d : E3} (hd : ‖d‖ = 1) : perp d d = 0 := by
  have h1 : (⟪d, d⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hd]; norm_num
  rw [perp, h1, one_smul, sub_self]

lemma norm_perp_le {d : E3} (hd : ‖d‖ = 1) (v : E3) : ‖perp d v‖ ≤ ‖v‖ := by
  have hexp : ‖perp d v‖ ^ 2 = ‖v‖ ^ 2 - (⟪v, d⟫ : ℝ) ^ 2 := by
    have h := norm_sub_sq_real v ((⟪v, d⟫ : ℝ) • d)
    rw [real_inner_smul_right, norm_smul, Real.norm_eq_abs, hd, mul_one, sq_abs] at h
    simp only [perp]
    rw [h]; ring
  have hle : ‖perp d v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [hexp]; nlinarith [sq_nonneg (⟪v, d⟫ : ℝ)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hle


open scoped Classical in
/-- **The multiscale anchored cover.** -/
theorem exists_looseGridCover {ι : Type*} {δ : NNReal} {N : ℕ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (s : Finset ι) (T : ι → Tube δ E3)
    (hB : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E3) 1)
    (hgap : ∀ k, 2 * ((Tube.gridScale δ N (k + 1) : NNReal) : ℝ)
      ≤ ((Tube.gridScale δ N k : NNReal) : ℝ))
    (hδle : ∀ k, k ≤ N → (δ : ℝ) ≤ ((Tube.gridScale δ N k : NNReal) : ℝ)) :
    ∃ cover : LooseGridCoverSystem s T N 4,
      (∀ k, k ≤ N → Set.InjOn (cover.tube k) (cover.indexSet k : Set ι)) ∧
      (∀ k, k ≤ N → ∀ V : Tube (Tube.gridScale δ N k) E3,
        (((cover.indexSet k).filter (fun j => ∃ i ∈ s, cover.assign k i = j ∧
          (T i).toConvexSpaceBody ≤ Kakeya.Tube.dilate V ((4 : ℝ) + 4))).card : ℕ)
          ≤ anchorOverlapConst) ∧
      (∀ k, ∀ j ∈ cover.indexSet k, ∃ i ∈ s, cover.assign k i = j) := by
  classical
  obtain ⟨v₀, hv₀ne⟩ := exists_ne (0 : E3)
  set u₀ : E3 := ‖v₀‖⁻¹ • v₀ with hu₀_def
  have hu₀ : ‖u₀‖ = 1 := by
    rw [hu₀_def, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv₀ne)]
  set ρ : ℕ → ℝ := fun k => ((Tube.gridScale δ N k : NNReal) : ℝ) with hρ_def
  have hρpos : ∀ k, 0 < ρ k := by
    intro k; exact_mod_cast Tube.gridScale_pos hδ N k
  have hρ1 : ∀ k, ρ k ≤ 1 := by
    intro k; exact_mod_cast Tube.gridScale_le_one hδ1 N k
  rcases s.eq_empty_or_nonempty with rfl | ⟨i₀, hi₀⟩
  · refine ⟨{ indexSet := fun _ => ∅
              assign := fun _ i => i
              tube := fun k _ => Tube.ofMidpointDirection (Tube.gridScale δ N k) 0 u₀ hu₀
              assign_mem := by simp
              le_dilate_tube_assign := by simp
              dir_close_tube_assign := by simp
              nested := by simp }, ?_, ?_, ?_⟩ <;> simp [anchorOverlapConst]
  haveI : Nonempty ι := ⟨i₀⟩
  -- the per-level nets
  have hnetD : ∀ k : ℕ, ∃ D : Finset E3, (∀ d ∈ D, ‖d‖ = 1) ∧
      (∀ x ∈ D, ∀ y ∈ D, x ≠ y → ρ k / 32 ≤ ‖x - y‖) ∧
      (∀ u : E3, ‖u‖ = 1 → ∃ d ∈ D, ‖u - d‖ ≤ 2 * (ρ k / 32)) := by
    intro k
    exact Tube.sphere_sep_net (E := E3) (by linarith [hρpos k]) (by linarith [hρ1 k])
  choose Dn hDn_unit hDn_sep hDn_cover using hnetD
  have hnetP : ∀ k : ℕ, ∃ P : Finset E3, (∀ p ∈ P, p ∈ Metric.closedBall (0 : E3) 3) ∧
      (∀ x ∈ P, ∀ y ∈ P, x ≠ y → ρ k / 64 ≤ ‖x - y‖) ∧
      (∀ m ∈ Metric.closedBall (0 : E3) 3, ∃ p ∈ P, ‖m - p‖ ≤ 2 * (ρ k / 64)) := by
    intro k
    exact Tube.midpoint_sep_net (E := E3) (by linarith [hρpos k])
  choose Pn hPn_loc hPn_sep hPn_cover using hnetP
  -- the rounding maps, made total
  have hrd : ∀ (k : ℕ) (u : E3), ∃ d : E3,
      ‖u‖ = 1 → (d ∈ Dn k ∧ ‖u - d‖ ≤ 2 * (ρ k / 32)) := by
    intro k u
    by_cases h : ‖u‖ = 1
    · obtain ⟨d, hd, hd2⟩ := hDn_cover k u h
      exact ⟨d, fun _ => ⟨hd, hd2⟩⟩
    · exact ⟨u₀, fun hc => absurd hc h⟩
  choose rD hrD using hrd
  have hrp : ∀ (k : ℕ) (m : E3), ∃ p : E3,
      m ∈ Metric.closedBall (0 : E3) 3 → (p ∈ Pn k ∧ ‖m - p‖ ≤ 2 * (ρ k / 64)) := by
    intro k m
    by_cases h : m ∈ Metric.closedBall (0 : E3) 3
    · obtain ⟨p, hp, hp2⟩ := hPn_cover k m h
      exact ⟨p, fun _ => ⟨hp, hp2⟩⟩
    · exact ⟨u₀, fun hc => absurd hc h⟩
  choose rP hrP using hrp
  -- the key, defined by downward iteration
  set stp : ℕ → (E3 × E3) → (E3 × E3) := fun k q =>
    (rP k (perp (rD k q.2) q.1), rD k q.2) with hstp_def
  set base : ι → E3 × E3 := fun i =>
    (rP N (perp (rD N (T i).direction) (T i).center), rD N (T i).direction) with hbase_def
  set key : ℕ → ι → E3 × E3 := fun k i => downIter N (base i) stp k with hkey_def
  have hkey_lt : ∀ k, k < N → ∀ i, key k i = stp k (key (k + 1) i) := by
    intro k hk i
    simp only [hkey_def]
    exact downIter_of_lt N (base i) stp hk
  have hkey_top : ∀ i, key N i = base i := by
    intro i
    simp only [hkey_def]
    exact downIter_of_not_lt N (base i) stp (lt_irrefl N)
  -- centres of members lie in the unit ball
  have hcen1 : ∀ i ∈ s, ‖(T i).center‖ ≤ 1 := by
    intro i hi
    have := hB i hi (center_mem_carrier hδ (T i))
    rwa [Metric.mem_closedBall, dist_zero_right] at this
  -- the downward invariant
  have hinv : ∀ i ∈ s, ∀ k, k ≤ N →
      (key k i).2 ∈ Dn k ∧ (key k i).1 ∈ Pn k ∧
      ‖(T i).direction - (key k i).2‖ ≤ ρ k / 8 ∧
      ‖(key k i).1 - perp ((key k i).2) ((T i).center)‖ ≤ 3 * ρ k / 16 := by
    intro i hi
    have H : ∀ l k, N - k = l → k ≤ N →
        (key k i).2 ∈ Dn k ∧ (key k i).1 ∈ Pn k ∧
        ‖(T i).direction - (key k i).2‖ ≤ ρ k / 8 ∧
        ‖(key k i).1 - perp ((key k i).2) ((T i).center)‖ ≤ 3 * ρ k / 16 := by
      intro l
      induction l with
      | zero =>
        intro k hlk hk
        have hkN : k = N := by omega
        subst hkN
        have hdN := hrD k (T i).direction (Tube.norm_direction (T i))
        have hdunit : ‖rD k (T i).direction‖ = 1 := hDn_unit k _ hdN.1
        have hball : perp (rD k (T i).direction) ((T i).center)
            ∈ Metric.closedBall (0 : E3) 3 := by
          rw [Metric.mem_closedBall, dist_zero_right]
          calc ‖perp (rD k (T i).direction) ((T i).center)‖ ≤ ‖(T i).center‖ :=
                norm_perp_le hdunit _
            _ ≤ 1 := hcen1 i hi
            _ ≤ 3 := by norm_num
        have hpN := hrP k _ hball
        rw [hkey_top i]
        refine ⟨hdN.1, hpN.1, ?_, ?_⟩
        · calc ‖(T i).direction - (base i).2‖ ≤ 2 * (ρ k / 32) := hdN.2
            _ ≤ ρ k / 8 := by linarith [hρpos k]
        · have := hpN.2
          calc ‖(base i).1 - perp ((base i).2) ((T i).center)‖
              = ‖perp (rD k (T i).direction) ((T i).center) - rP k
                  (perp (rD k (T i).direction) ((T i).center))‖ := by
                rw [← norm_neg]; simp only [hbase_def]; congr 1; module
            _ ≤ 2 * (ρ k / 64) := this
            _ ≤ 3 * ρ k / 16 := by linarith [hρpos k]
      | succ l ih =>
        intro k hlk hk
        have hkN : k < N := by omega
        obtain ⟨hd1, hp1, hdir1, hpos1⟩ := ih (k + 1) (by omega) (by omega)
        set d : E3 := (key (k + 1) i).2 with hd_def
        set p : E3 := (key (k + 1) i).1 with hp_def
        have hdunit : ‖d‖ = 1 := hDn_unit (k + 1) _ hd1
        have hrDspec := hrD k d hdunit
        set d' : E3 := rD k d with hd'_def
        have hd'unit : ‖d'‖ = 1 := hDn_unit k _ hrDspec.1
        have hball : perp d' p ∈ Metric.closedBall (0 : E3) 3 := by
          rw [Metric.mem_closedBall, dist_zero_right]
          have hp3 : ‖p‖ ≤ 3 := by
            have := hPn_loc (k + 1) _ hp1
            rwa [Metric.mem_closedBall, dist_zero_right] at this
          exact le_trans (norm_perp_le hd'unit _) hp3
        have hrPspec := hrP k (perp d' p) hball
        have hkeyk : key k i = (rP k (perp d' p), d') := by
          rw [hkey_lt k hkN i]
        have hgapk := hgap k
        have hdd' : ‖d - d'‖ ≤ 2 * (ρ k / 32) := hrDspec.2
        rw [hkeyk]
        refine ⟨hrDspec.1, hrPspec.1, ?_, ?_⟩
        · calc ‖(T i).direction - d'‖
              ≤ ‖(T i).direction - d‖ + ‖d - d'‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
            _ ≤ ρ (k + 1) / 8 + 2 * (ρ k / 32) := add_le_add hdir1 hdd'
            _ ≤ ρ k / 8 := by linarith
        · have hd'd : perp d' d = perp d' (d - d') := by
            rw [perp_sub, perp_self hd'unit, sub_zero]
          have hid : perp d' (p - (T i).center)
              = perp d' (p - perp d ((T i).center))
                - (⟪(T i).center, d⟫ : ℝ) • perp d' d := by
            rw [← perp_smul, ← perp_sub]
            congr 1
            simp only [perp]
            module
          have hinner1 : |(⟪(T i).center, d⟫ : ℝ)| ≤ 1 := by
            calc |(⟪(T i).center, d⟫ : ℝ)| ≤ ‖(T i).center‖ * ‖d‖ := abs_real_inner_le_norm _ _
              _ ≤ 1 * 1 := mul_le_mul (hcen1 i hi) (le_of_eq hdunit) (norm_nonneg _) (by norm_num)
              _ = 1 := by norm_num
          have hb2 : ‖perp d' (p - (T i).center)‖ ≤ 3 * ρ (k + 1) / 16 + ρ k / 16 := by
            rw [hid]
            calc ‖perp d' (p - perp d ((T i).center))
                    - (⟪(T i).center, d⟫ : ℝ) • perp d' d‖
                ≤ ‖perp d' (p - perp d ((T i).center))‖
                  + ‖(⟪(T i).center, d⟫ : ℝ) • perp d' d‖ := norm_sub_le _ _
              _ ≤ 3 * ρ (k + 1) / 16 + ρ k / 16 := by
                  refine add_le_add ?_ ?_
                  · exact le_trans (norm_perp_le hd'unit _) hpos1
                  · rw [norm_smul, Real.norm_eq_abs, hd'd]
                    calc |(⟪(T i).center, d⟫ : ℝ)| * ‖perp d' (d - d')‖
                        ≤ 1 * ‖d - d'‖ :=
                          mul_le_mul hinner1 (norm_perp_le hd'unit _) (norm_nonneg _)
                            (by norm_num)
                      _ ≤ 1 * (2 * (ρ k / 32)) := by
                          exact mul_le_mul_of_nonneg_left hdd' (by norm_num)
                      _ = ρ k / 16 := by ring
          have hb1 : ‖rP k (perp d' p) - perp d' p‖ ≤ 2 * (ρ k / 64) := by
            rw [← norm_neg, neg_sub]
            exact hrPspec.2
          calc ‖rP k (perp d' p) - perp d' ((T i).center)‖
              ≤ ‖rP k (perp d' p) - perp d' p‖ + ‖perp d' p - perp d' ((T i).center)‖ :=
                norm_sub_le_norm_sub_add_norm_sub _ _ _
            _ ≤ 2 * (ρ k / 64) + (3 * ρ (k + 1) / 16 + ρ k / 16) := by
                refine add_le_add hb1 ?_
                rw [← perp_sub]
                exact hb2
            _ ≤ 3 * ρ k / 16 := by linarith
    exact fun k hk => H (N - k) k rfl hk
  have hgs : ∀ m : ℕ, ((Tube.gridScale δ N m : NNReal) : ℝ) = ρ m := fun _ => rfl
  -- the cell representatives
  have hex : ∀ (k : ℕ) (c : E3 × E3), ∃ j : ι,
      (∃ j', j' ∈ s ∧ key k j' = c) → (j ∈ s ∧ key k j = c) := by
    intro k c
    by_cases h : ∃ j', j' ∈ s ∧ key k j' = c
    · obtain ⟨j, hj, hkj⟩ := h
      exact ⟨j, fun _ => ⟨hj, hkj⟩⟩
    · exact ⟨i₀, fun hc => absurd hc h⟩
  choose cellRep hcellRep using hex
  set asg : ℕ → ι → ι := fun k i => cellRep k (key k i) with hasg_def
  have hasg_app : ∀ k i, asg k i = cellRep k (key k i) := fun _ _ => rfl
  have hasg_spec : ∀ k, ∀ i ∈ s, asg k i ∈ s ∧ key k (asg k i) = key k i :=
    fun k i hi => hcellRep k (key k i) ⟨i, hi, rfl⟩
  have hasg_mem : ∀ k, ∀ i ∈ s, asg k i ∈ s := fun k i hi => (hasg_spec k i hi).1
  have hasg_key : ∀ k, ∀ i ∈ s, key k (asg k i) = key k i := fun k i hi => (hasg_spec k i hi).2
  have hasg_idem : ∀ k, ∀ i ∈ s, asg k (asg k i) = asg k i := by
    intro k i hi
    rw [hasg_app k (asg k i), hasg_key k i hi, ← hasg_app k i]
  set idx : ℕ → Finset ι := fun k => s.image (asg k) with hidx_def
  have hidx_asg : ∀ k, ∀ j ∈ idx k, asg k j = j := by
    intro k j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact hasg_idem k i hi
  have hidx_s : ∀ k, ∀ j ∈ idx k, j ∈ s := by
    intro k j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact hasg_mem k i hi
  -- the nodes
  set ndAt : (k : ℕ) → E3 → E3 → Tube (Tube.gridScale δ N k) E3 := fun k m u =>
    if h : ‖u‖ = 1 then Tube.ofMidpointDirection (Tube.gridScale δ N k) m u h
    else Tube.ofMidpointDirection (Tube.gridScale δ N k) m u₀ hu₀ with hndAt_def
  set nd : (k : ℕ) → ι → Tube (Tube.gridScale δ N k) E3 :=
    fun k j => ndAt k (key k j).1 (key k j).2 with hnd_def
  have hnd_c : ∀ k j, ‖(key k j).2‖ = 1 → (nd k j).center = (key k j).1 := by
    intro k j h
    simp only [hnd_def, hndAt_def, dif_pos h]
    simp [Tube.center, Tube.ofMidpointDirection, midpoint_eq_smul_add]
    module
  have hnd_d : ∀ k j, ‖(key k j).2‖ = 1 → (nd k j).direction = (key k j).2 := by
    intro k j h
    simp only [hnd_def, hndAt_def, dif_pos h]
    simp [Tube.direction, Tube.ofMidpointDirection]
    module
  have hfield1 : ∀ k, k ≤ N → ∀ i ∈ s,
      (T i).toConvexSpaceBody ≤ Kakeya.Tube.dilate (nd k (asg k i)) 4 := by
    intro k hk i hi
    obtain ⟨hd1, hp1, hdir1, hpos1⟩ := hinv i hi k hk
    have hdunit : ‖(key k i).2‖ = 1 := hDn_unit k _ hd1
    have hkeq : key k (asg k i) = key k i := hasg_key k i hi
    have hc : (nd k (asg k i)).center = (key k i).1 := by
      rw [hnd_c k (asg k i) (by rw [hkeq]; exact hdunit), hkeq]
    have hd : (nd k (asg k i)).direction = (key k i).2 := by
      rw [hnd_d k (asg k i) (by rw [hkeq]; exact hdunit), hkeq]
    refine le_dilate_of_through_point (nd k (asg k i)) (K' := 4) (r := 3 * ρ k / 16)
      (θ := ρ k / 8) (by norm_num) (x := (T i).center)
      (s₀ := (⟪(T i).center, (key k i).2⟫ : ℝ)) ?_ ?_ (T i)
      (center_mem_carrier hδ (T i)) (σ := 1) (by norm_num) ?_ ?_
    · have hb : |(⟪(T i).center, (key k i).2⟫ : ℝ)| ≤ 1 := by
        calc |(⟪(T i).center, (key k i).2⟫ : ℝ)| ≤ ‖(T i).center‖ * ‖(key k i).2‖ :=
              abs_real_inner_le_norm _ _
          _ ≤ 1 * 1 := mul_le_mul (hcen1 i hi) (le_of_eq hdunit) (norm_nonneg _) (by norm_num)
          _ = 1 := by norm_num
      linarith
    · rw [hc, hd, dist_eq_norm,
        show (T i).center - ((key k i).1 + (⟪(T i).center, (key k i).2⟫ : ℝ) • (key k i).2)
            = -((key k i).1 - perp ((key k i).2) ((T i).center)) from by
          simp only [perp]; module, norm_neg]
      exact hpos1
    · rw [hd, one_smul]; exact hdir1
    · rw [hgs k]
      have h1 := hδle k hk
      rw [hgs k] at h1
      linarith [hρpos k]
  have hfield2 : ∀ k, k ≤ N → ∀ i ∈ s, ∃ σ : ℝ, |σ| = 1 ∧
      ‖(T i).direction - σ • (nd k (asg k i)).direction‖
        ≤ ((Tube.gridScale δ N k : NNReal) : ℝ) / 4 := by
    intro k hk i hi
    obtain ⟨hd1, hp1, hdir1, hpos1⟩ := hinv i hi k hk
    have hdunit : ‖(key k i).2‖ = 1 := hDn_unit k _ hd1
    have hkeq : key k (asg k i) = key k i := hasg_key k i hi
    have hd : (nd k (asg k i)).direction = (key k i).2 := by
      rw [hnd_d k (asg k i) (by rw [hkeq]; exact hdunit), hkeq]
    refine ⟨1, by norm_num, ?_⟩
    rw [hd, one_smul, hgs k]
    linarith [hρpos k]
  have hfield3 : ∀ k, k + 1 ≤ N → ∀ i ∈ s, ∀ j ∈ s,
      asg (k + 1) i = asg (k + 1) j → asg k i = asg k j := by
    intro k hk i hi j hj heq
    have h1 : key (k + 1) i = key (k + 1) j := by
      rw [← hasg_key (k + 1) i hi, ← hasg_key (k + 1) j hj, heq]
    have h2 : key k i = key k j := by
      rw [hkey_lt k (by omega) i, hkey_lt k (by omega) j, h1]
    rw [hasg_app k i, hasg_app k j, h2]
  have hinjOn : ∀ k, k ≤ N → Set.InjOn (nd k) (idx k : Set ι) := by
    intro k hk j hj j' hj' heq
    have hjidx : j ∈ idx k := Finset.mem_coe.mp hj
    have hj'idx : j' ∈ idx k := Finset.mem_coe.mp hj'
    obtain ⟨hd1, -, -, -⟩ := hinv j (hidx_s k j hjidx) k hk
    obtain ⟨hd1', -, -, -⟩ := hinv j' (hidx_s k j' hj'idx) k hk
    have hu : ‖(key k j).2‖ = 1 := hDn_unit k _ hd1
    have hu' : ‖(key k j').2‖ = 1 := hDn_unit k _ hd1'
    have hc : (key k j).1 = (key k j').1 := by rw [← hnd_c k j hu, ← hnd_c k j' hu', heq]
    have hd : (key k j).2 = (key k j').2 := by rw [← hnd_d k j hu, ← hnd_d k j' hu', heq]
    have hkk : key k j = key k j' := Prod.ext hc hd
    have hEq : asg k j = asg k j' := by rw [hasg_app k j, hasg_app k j', hkk]
    rwa [hidx_asg k j hjidx, hidx_asg k j' hj'idx] at hEq
  have hbo : ∀ k, k ≤ N → ∀ V : Tube (Tube.gridScale δ N k) E3,
      ((((idx k).filter (fun j => ∃ i ∈ s, asg k i = j ∧
        (T i).toConvexSpaceBody ≤ Kakeya.Tube.dilate V ((4 : ℝ) + 4))).card : ℕ))
        ≤ anchorOverlapConst := by
    intro k hk V
    set F := (idx k).filter (fun j => ∃ i ∈ s, asg k i = j ∧
      (T i).toConvexSpaceBody ≤ Kakeya.Tube.dilate V ((4 : ℝ) + 4)) with hF_def
    have hFprop : ∀ j ∈ F, ‖(key k j).1 - axisFoot V‖ ≤ 83 * ρ k ∧
        (‖(key k j).2 - V.direction‖ ≤ 33 * ρ k ∨
          ‖(key k j).2 - (-V.direction)‖ ≤ 33 * ρ k) := by
      intro j hj
      obtain ⟨hjidx, i, hi, haij, hiV⟩ := Finset.mem_filter.mp hj
      obtain ⟨hd1, hp1, hdir1, hpos1⟩ := hinv i hi k hk
      have hdunit : ‖(key k i).2‖ = 1 := hDn_unit k _ hd1
      have h8 : (T i).toConvexSpaceBody ≤ Kakeya.Tube.dilate V 8 := by
        have h44 : ((4 : ℝ) + 4) = 8 := by norm_num
        rwa [h44] at hiV
      obtain ⟨σ, hσ, hdd, hfoot⟩ :=
        anchor_near_axisFoot (T i) V hdunit (hcen1 i hi) hδ
          (by rw [hgs k]; linarith [hρpos k]) h8
      subst haij
      rw [hasg_key k i hi]
      constructor
      · calc ‖(key k i).1 - axisFoot V‖
            ≤ ‖(key k i).1 - anchorAt (T i) ((key k i).2)‖
              + ‖anchorAt (T i) ((key k i).2) - axisFoot V‖ :=
              norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ ≤ 3 * ρ k / 16 + 82 * ρ k := by
              refine add_le_add hpos1 ?_
              rw [hgs k] at hfoot
              exact hfoot
          _ ≤ 83 * ρ k := by linarith [hρpos k]
      · rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp hσ with h | h
        · left
          rw [h, one_smul] at hdd
          rw [hgs k] at hdd
          exact hdd
        · right
          rw [h] at hdd
          rw [hgs k] at hdd
          simpa using hdd
    set Fp := F.filter (fun j => ‖(key k j).2 - V.direction‖ ≤ 33 * ρ k) with hFp_def
    set Fm := F \ Fp with hFm_def
    have hcard_bound : ∀ (G : Finset ι) (cy : E3), G ⊆ F →
        (∀ j ∈ G, ‖(key k j).2 - cy‖ ≤ 33 * ρ k) → G.card ≤ 21249 ^ 6 := by
      intro G cy hGF hGy
      have hsep : ∀ x ∈ G, ∀ y ∈ G, x ≠ y →
          ρ k / 64 ≤ ‖(key k x).1 - (key k y).1‖ + ‖(key k x).2 - (key k y).2‖ := by
        intro x hx y hy hxy
        have hxidx : x ∈ idx k := (Finset.mem_filter.mp (hGF hx)).1
        have hyidx : y ∈ idx k := (Finset.mem_filter.mp (hGF hy)).1
        obtain ⟨hdx, hpx, -, -⟩ := hinv x (hidx_s k x hxidx) k hk
        obtain ⟨hdy, hpy, -, -⟩ := hinv y (hidx_s k y hyidx) k hk
        by_cases hp : (key k x).1 = (key k y).1
        · have hdne : (key k x).2 ≠ (key k y).2 := by
            intro hd
            apply hxy
            have hkk : key k x = key k y := Prod.ext hp hd
            have hEq : asg k x = asg k y := by rw [hasg_app k x, hasg_app k y, hkk]
            rwa [hidx_asg k x hxidx, hidx_asg k y hyidx] at hEq
          have hsd := hDn_sep k _ hdx _ hdy hdne
          have h0 : (0:ℝ) ≤ ‖(key k x).1 - (key k y).1‖ := norm_nonneg _
          linarith [hρpos k]
        · have hsp := hPn_sep k _ hpx _ hpy hp
          have h0 : (0:ℝ) ≤ ‖(key k x).2 - (key k y).2‖ := norm_nonneg _
          linarith
      have hpack := Tube.card_le_of_L1_separated_in_box (E := E3) G
        (fun j => (key k j).1) (fun j => (key k j).2) (axisFoot V) cy
        (R := 83 * ρ k) (r := ρ k / 64) (by linarith [hρpos k]) hsep
        (fun j hj => (hFprop j (hGF hj)).1)
        (fun j hj => (hGy j hj).trans (by linarith [hρpos k]))
      have hfr : Module.finrank ℝ E3 = 3 := by simp [E3]
      rw [hfr] at hpack
      have hval : ((83 * ρ k + (ρ k / 64) / 4) / ((ρ k / 64) / 4)) = 21249 := by
        rw [div_eq_iff (by have := hρpos k; intro hc; nlinarith)]
        ring
      rw [hval] at hpack
      exact_mod_cast hpack
    have hFp_card : Fp.card ≤ 21249 ^ 6 :=
      hcard_bound Fp V.direction (Finset.filter_subset _ _)
        (fun j hj => (Finset.mem_filter.mp hj).2)
    have hFm_card : Fm.card ≤ 21249 ^ 6 := by
      refine hcard_bound Fm (-V.direction) Finset.sdiff_subset ?_
      intro j hj
      obtain ⟨hjF, hjn⟩ := Finset.mem_sdiff.mp hj
      rcases (hFprop j hjF).2 with h | h
      · exact absurd (Finset.mem_filter.mpr ⟨hjF, h⟩) hjn
      · exact h
    have hsplit : F.card ≤ Fp.card + Fm.card := by
      have hFeq : F.card = (Fp ∪ Fm).card := by
        congr 1
        rw [hFm_def, Finset.union_sdiff_of_subset (Finset.filter_subset _ _)]
      rw [hFeq]
      exact Finset.card_union_le _ _
    calc F.card ≤ Fp.card + Fm.card := hsplit
      _ ≤ 21249 ^ 6 + 21249 ^ 6 := Nat.add_le_add hFp_card hFm_card
      _ = anchorOverlapConst := by rw [anchorOverlapConst]; ring
  refine ⟨{ indexSet := idx
            assign := asg
            tube := nd
            assign_mem := fun k _ i hi => Finset.mem_image_of_mem (asg k) hi
            le_dilate_tube_assign := hfield1
            dir_close_tube_assign := hfield2
            nested := hfield3 }, hinjOn, hbo, ?_⟩
  intro k j hj
  obtain ⟨i, hi, hij⟩ := Finset.mem_image.mp hj
  exact ⟨i, hi, hij⟩

/-! ## Packaging, and the essential-distinctness question

Two further pieces, for the two consumers of this hierarchy.

**(a) The residue, named.**  `Kakeya.LooseUniform.LooseUniformTubeSet.ofCoverBrackets` turns the
output of `Kakeya.LooseUniform.exists_looseGridCover` into a
`Kakeya.LooseUniform.LooseUniformTubeSet` as soon as GWZ Definition 2.1(iii)'s two-sided class
bracket is supplied.  So the *whole* remaining obligation of the loose Definition-2.1 datum is
Definition 2.1(iii), which is geometry-free (`Tube.exists_pruned_subset_noroot_notop`) and costs a
refinement; the geometry is done.

**(b) Essential distinctness of the nodes is a DIFFERENT hierarchy, not this one.**  The nodes
produced here are **not** pairwise essentially distinct, and cannot be made so while
`Kakeya.LooseUniform.LooseGridCoverSystem.dir_close_tube_assign` is read at `ρ_k/4`: that clause
forces the node directions in use to be a `ρ_k/4`-dense subset of the sphere, hence to contain
pairs at distance `≤ ρ_k/2`, and two unit `ρ_k`-tubes whose directions differ by `≤ ρ_k/2` and
whose axes pass within `ρ_k` of each other overlap in almost their whole volume.  What is offered
instead, for the consumers that need Definition 2.1(ii) itself
(`Kakeya.ML2Core.hstep8_of_essDistinct`), is the generic selector
`Kakeya.LooseUniform.exists_essDistinct_subfamily`: a **maximal** essentially distinct subfamily of
an arbitrary finite tube family, together with the maximality clause "every discarded member fails
to be essentially distinct from a kept one", which is what converts a count on the full family into
a count on the essentially distinct one.
-/


/-- **The residue named: Definition 2.1(iii) and nothing else.** -/
noncomputable def LooseUniformTubeSet.ofCoverBrackets {ι : Type*} {δ : NNReal} {s : Finset ι}
    {T : ι → Tube δ E3} {N : ℕ} (cover : LooseGridCoverSystem s T N 4)
    (branchingN : ℕ → NNReal) {C : NNReal}
    (hinj : ∀ k, k ≤ N → Set.InjOn (cover.tube k) (cover.indexSet k : Set ι))
    (hbo : ∀ k, k ≤ N → ∀ V : Tube (Tube.gridScale δ N k) E3,
      (open scoped Classical in
        ((cover.indexSet k).filter (fun j => ∃ i ∈ s, cover.assign k i = j ∧
          (T i).toConvexSpaceBody ≤ Kakeya.Tube.dilate V ((4 : ℝ) + 4))).card)
        ≤ anchorOverlapConst)
    (hup : ∀ k, k ≤ N → ∀ j ∈ cover.indexSet k,
      ((Tube.coverClass s (cover.assign k) j).card : NNReal) ≤ C * branchingN k)
    (hlo : ∀ k, k ≤ N → ∀ j ∈ cover.indexSet k,
      branchingN k ≤ C * ((Tube.coverClass s (cover.assign k) j).card : NNReal)) :
    LooseUniformTubeSet s T N 4 (max C (anchorOverlapConst : NNReal)) where
  cover := cover
  branchingN := branchingN
  tube_injOn := hinj
  boundedOverlapDil k hk V := le_trans (by exact_mod_cast hbo k hk V) (le_max_right _ _)
  card_class_le k hk j hj := (hup k hk j hj).trans (mul_le_mul' (le_max_left _ _) le_rfl)
  le_card_class k hk j hj := (hlo k hk j hj).trans (mul_le_mul' (le_max_left _ _) le_rfl)

theorem volume_tube_carrier_ne_zero {σ : NNReal} (hσ : 0 < σ) (W : Tube σ E3) :
    volume W.carrier ≠ 0 := by
  have hvol := Tube.le_volume (E := E3) W
  have hpos : (0 : ENNReal) < (Tube.le_volume.c (Module.finrank ℝ E3) : ENNReal)
      * (σ : ENNReal) ^ ((Module.finrank ℝ E3 : ℕ) - 1) := by
    refine ENNReal.mul_pos ?_ ?_
    · simpa using (ne_of_gt (Tube.le_volume.c_pos (Module.finrank ℝ E3)))
    · simp only [ne_eq, pow_eq_zero_iff', not_and, not_not]
      intro h0
      exact absurd (by exact_mod_cast h0 : σ = 0) (ne_of_gt hσ)
  exact ne_of_gt (lt_of_lt_of_le hpos hvol)

theorem volume_tube_carrier_ne_top {σ : NNReal} (W : Tube σ E3) : volume W.carrier ≠ ⊤ :=
  ne_top_of_le_ne_top W.isCompact.measure_ne_top le_rfl

/-- **A maximal essentially distinct subfamily.** -/
theorem exists_essDistinct_subfamily {α : Type*} {σ : NNReal} (hσ : 0 < σ)
    (S : Finset α) (W : α → Tube σ E3) :
    ∃ P : Finset α, P ⊆ S ∧
      ((P : Set α).Pairwise fun a b => IsEssentiallyDistinct (W a).carrier (W b).carrier) ∧
      (∀ r ∈ S, ∃ w ∈ P, ¬ IsEssentiallyDistinct (W r).carrier (W w).carrier) := by
  classical
  set d : α → α → ℝ := fun a b =>
    if IsEssentiallyDistinct (W a).carrier (W b).carrier then (1 : ℝ) else 0 with hd_def
  have hd_self : ∀ a, d a a < 1 := by
    intro a
    have hns : ¬ IsEssentiallyDistinct (W a).carrier (W a).carrier :=
      not_isEssentiallyDistinct_self (volume_tube_carrier_ne_zero hσ (W a))
        (volume_tube_carrier_ne_top (W a))
    simp only [hd_def, if_neg hns]
    norm_num
  have hd_symm : ∀ a b, d a b = d b a := by
    intro a b
    by_cases h : IsEssentiallyDistinct (W a).carrier (W b).carrier
    · simp only [hd_def, if_pos h, if_pos (isEssentiallyDistinct_symm h)]
    · simp only [hd_def, if_neg h, if_neg (fun hc => h (isEssentiallyDistinct_symm hc))]
  obtain ⟨P, hPsub, hPsep, hPcov⟩ :=
    exists_maximal_separated_finset (ε := (1 : ℝ)) S d hd_self hd_symm
  refine ⟨P, hPsub, ?_, ?_⟩
  · intro a ha b hb hab
    have h := hPsep a (Finset.mem_coe.mp ha) b (Finset.mem_coe.mp hb) hab
    by_contra hcon
    simp only [hd_def, if_neg hcon] at h
    norm_num at h
  · intro r hr
    obtain ⟨w, hw, hwd⟩ := hPcov r hr
    refine ⟨w, hw, ?_⟩
    intro hcon
    simp only [hd_def, if_pos hcon] at hwd
    norm_num at hwd


/-! ## From the cover to GWZ Definition 2.1 and Definition 2.2, on a refinement

The geometry is finished above.  What is left of the loose Definition-2.1 datum is Definition
2.1(iii)'s two-sided class bracket, and of Definition 2.2 its four shading brackets; both are
**geometry-free** and both are paid for by a refinement.  This section runs the two existing engines
on the anchored cover.

* **Definition 2.1(iii)** — `Tube.exists_pruned_subset_noroot_notop` takes only `assign`,
  `assign_mem`, `nested` and a bound on the level-`0` index set.  The last of these is supplied by
  the cover's own `boundedOverlapDil` at `k = 0`, where `Tube.gridScale δ N 0 = 1` and the
  `8`-dilate of the unit tube through the origin swallows the whole unit ball
  (`Kakeya.LooseUniform.card_indexSet_zero_le`) — so the pruning constant is again the absolute
  `anchorOverlapConst`, not a new one.  Retention: `(anchorOverlapConst · (⌊log₂|s|⌋+1))^N`, i.e.
  `δ^{-α}` at the grid length after `Tube.exists_threshold_polylog_pow_ssfGridLen_le`.
* **Definition 2.2** — `ShadedTube.exists_balanced_shadeRefinement_of_cover` wants a *bare*
  `Tube.GridCoverSystem` over an arbitrary tube family at an arbitrary thickness, and reads only
  its `assign`.  `Kakeya.LooseUniform.trivialGridCover` is that carrier: the constant family at
  thickness `1`, whose containment and nesting fields are `le_refl` after
  `Kakeya.LooseUniform.gridScale_one`.  This is the manoeuvre  predicted and did
  not compile.  Retention: `(⌊log₂|s|⌋+1)^{2N+2}` of shade mass, i.e. `δ^{-α'}` at the grid length.

The end products are `Kakeya.LooseUniform.exists_looseUniformTubeSet_subfamily_ssf` and
`Kakeya.LooseUniform.exists_looseShadedUniformTubeSet_subfamily_ssf`, stated for an **arbitrary**
family, and `Kakeya.LooseUniform.exists_looseShaded_subfamily_of_config`, the same at a
`Kakeya.VeryNotSticky` and at the constant `max cfg.C₀ anchorOverlapConst`.

**What is still NOT discharged.**  Conjunct 6's `∃ 𝒱` binds the datum on `cfg.s` itself; what is
produced here lives on a **subfamily** `s' ⊆ cfg.s` with a shrunk shading, exactly as GWZ's
l.191-193 produces it.  Closing conjunct 6 therefore needs the *configuration producer* to name the
refined family as the new `cfg.s` — which is what
`Kakeya.VeryNotSticky.exists_config_of_slackCut_at` already does for the exact datum, and which is
not touched here.  **Nothing in this file discharges
conjunct 6.**
-/

open scoped Classical in
/-- The level-`0` index set of an anchored cover is bounded by the absolute overlap constant. -/
theorem card_indexSet_zero_le {ι : Type*} {δ : NNReal} {N : ℕ} {s : Finset ι} {T : ι → Tube δ E3}
    (hB : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E3) 1)
    (cover : LooseGridCoverSystem s T N 4)
    (hsurj : ∀ j ∈ cover.indexSet 0, ∃ i ∈ s, cover.assign 0 i = j)
    (hbo : ∀ V : Tube (Tube.gridScale δ N 0) E3,
      (((cover.indexSet 0).filter (fun j => ∃ i ∈ s, cover.assign 0 i = j ∧
        (T i).toConvexSpaceBody ≤ Kakeya.Tube.dilate V ((4 : ℝ) + 4))).card : ℕ)
        ≤ anchorOverlapConst) :
    (cover.indexSet 0).card ≤ anchorOverlapConst := by
  classical
  obtain ⟨v₀, hv₀ne⟩ := exists_ne (0 : E3)
  have hu₀ : ‖(‖v₀‖⁻¹ • v₀ : E3)‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv₀ne)]
  set V₀ : Tube (Tube.gridScale δ N 0) E3 :=
    Tube.ofMidpointDirection (Tube.gridScale δ N 0) 0 _ hu₀ with hV₀
  have hcenter : V₀.center = 0 := by
    simp [hV₀, Tube.center, Tube.ofMidpointDirection, midpoint_eq_smul_add]
  have hρ0 : ((Tube.gridScale δ N 0 : NNReal) : ℝ) = 1 := by
    rw [Tube.gridScale_zero]; norm_num
  have hall : ∀ i ∈ s, (T i).toConvexSpaceBody ≤ Kakeya.Tube.dilate V₀ ((4 : ℝ) + 4) := by
    intro i hi z hz
    have hz1 : ‖z‖ ≤ 1 := by
      have := hB i hi hz
      rwa [Metric.mem_closedBall, dist_zero_right] at this
    have h8 : ((4 : ℝ) + 4) = 8 := by norm_num
    rw [h8]
    refine Kakeya.Tube.mem_dilate_of_dist_axis_le V₀ (by norm_num : (0:ℝ) < 8)
      (s := 0) (by norm_num) ?_
    rw [hcenter, zero_smul, add_zero, dist_zero_right, hρ0]
    linarith
  have heq : (cover.indexSet 0).filter (fun j => ∃ i ∈ s, cover.assign 0 i = j ∧
      (T i).toConvexSpaceBody ≤ Kakeya.Tube.dilate V₀ ((4 : ℝ) + 4)) = cover.indexSet 0 := by
    refine Finset.filter_true_of_mem ?_
    intro j hj
    obtain ⟨i, hi, hij⟩ := hsurj j hj
    exact ⟨i, hi, hij, hall i hi⟩
  have := hbo V₀
  rwa [heq] at this


open scoped Classical in
/-- **(3) GWZ Definition 2.1 in the loose model, on a subfamily.** -/
theorem exists_looseUniformTubeSet_subfamily {ι : Type*} {δ : NNReal} (N : ℕ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hN : 0 < N)
    (hδ0 : δ ≤ (16 : NNReal) ^ (-(N : ℝ)))
    (s : Finset ι) (T : ι → Tube δ E3)
    (hB : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E3) 1) :
    ∃ s' ⊆ s,
      (s.card : ℝ)
          ≤ ((anchorOverlapConst : ℝ) * ((⌊Real.logb 2 (s.card : ℝ)⌋₊ : ℝ) + 1)) ^ N
            * (s'.card : ℝ) ∧
        Nonempty (LooseUniformTubeSet s' T N 4 (max 2 (anchorOverlapConst : NNReal))) := by
  classical
  have hC₀one : (1 : ℝ) ≤ (anchorOverlapConst : ℝ) := by
    rw [anchorOverlapConst]; norm_num
  have hC₀pos : (0 : ℝ) < (anchorOverlapConst : ℝ) := by linarith
  -- the grid gap, from `δ ≤ 16^{-N}`
  have hδnonneg : (0 : ℝ) ≤ (δ : ℝ) := (δ : NNReal).coe_nonneg
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
  have hgap : (δ : ℝ) ^ ((1 : ℝ) / (N : ℝ)) ≤ 1 / 2 := by
    have hδle16R : (δ : ℝ) ≤ (16 : ℝ) ^ (-(N : ℝ)) := by
      have hcast : (δ : ℝ) ≤ (((16 : NNReal) ^ (-(N : ℝ)) : NNReal) : ℝ) :=
        NNReal.coe_le_coe.mpr hδ0
      simpa [NNReal.coe_rpow] using hcast
    have hprod : (-(N : ℝ)) * ((1 : ℝ) / (N : ℝ)) = -1 := by field_simp
    calc (δ : ℝ) ^ ((1 : ℝ) / (N : ℝ)) ≤ ((16 : ℝ) ^ (-(N : ℝ))) ^ ((1 : ℝ) / (N : ℝ)) :=
          Real.rpow_le_rpow hδnonneg hδle16R (by positivity)
      _ = (1 : ℝ) / 16 := by
          rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 16), hprod]; norm_num
      _ ≤ 1 / 2 := by norm_num
  have hgapρ : ∀ k, 2 * ((Tube.gridScale δ N (k + 1) : NNReal) : ℝ)
      ≤ ((Tube.gridScale δ N k : NNReal) : ℝ) := by
    intro k
    have h := Tube.rho_scale_gap hδ hN hgap k
    simpa [Tube.gridScale, NNReal.coe_rpow] using h
  have hδle : ∀ k, k ≤ N → (δ : ℝ) ≤ ((Tube.gridScale δ N k : NNReal) : ℝ) := by
    intro k hk
    have h1 := Tube.gridScale_antitone hδ hδ1 N hk
    rw [Tube.gridScale_self δ hN] at h1
    exact_mod_cast h1
  rcases s.eq_empty_or_nonempty with rfl | hs_ne
  · obtain ⟨cover, hinj, hbo, hsurj⟩ := exists_looseGridCover hδ hδ1 ∅ T (by simp) hgapρ hδle
    refine ⟨∅, Finset.Subset.refl _, by simp, ⟨?_⟩⟩
    exact LooseUniformTubeSet.ofCoverBrackets cover (fun _ => 0) (C := 2)
      (fun k hk => hinj k hk) (fun k hk V => hbo k hk V)
      (fun k hk j hj => by simp [Tube.coverClass])
      (fun k hk j hj => by simp)
  obtain ⟨cover, hinj, hbo, hsurj⟩ := exists_looseGridCover hδ hδ1 s T hB hgapρ hδle
  have hC₀ : ((cover.indexSet 0).card : ℝ) ≤ (anchorOverlapConst : ℝ) := by
    exact_mod_cast card_indexSet_zero_le hB cover (hsurj 0) (hbo 0 (Nat.zero_le N))
  obtain ⟨s', N₂, parent', hs'_sub, hs'_card, h_parent'_sub, h_assign'_mem, h_active, h_band⟩ :=
    Tube.exists_pruned_subset_noroot_notop s N hs_ne cover.indexSet cover.assign
      (fun k hk i hi => cover.assign_mem k hk i hi)
      (fun k hk i j hi hj h => cover.nested k (by omega) i hi j hj h)
      (anchorOverlapConst : ℝ) hC₀pos hC₀
  set B : ℝ := (⌊Real.logb 2 (s.card : ℝ)⌋₊ : ℝ) + 1 with hB_def
  have hBpos : (0 : ℝ) < B := by rw [hB_def]; positivity
  have hcard_final : (s.card : ℝ) ≤ ((anchorOverlapConst : ℝ) * B) ^ N * (s'.card : ℝ) := by
    have hd : (0 : ℝ) < (anchorOverlapConst : ℝ) * (B ^ N) := mul_pos hC₀pos (pow_pos hBpos N)
    have hadiv := (div_le_iff₀ hd).mp hs'_card
    have hCN : (anchorOverlapConst : ℝ) ≤ (anchorOverlapConst : ℝ) ^ N := by
      calc (anchorOverlapConst : ℝ) = (anchorOverlapConst : ℝ) ^ 1 := by rw [pow_one]
        _ ≤ (anchorOverlapConst : ℝ) ^ N := pow_le_pow_right₀ hC₀one hN
    have hmul : (anchorOverlapConst : ℝ) * B ^ N ≤ ((anchorOverlapConst : ℝ) * B) ^ N := by
      calc (anchorOverlapConst : ℝ) * B ^ N
          ≤ (anchorOverlapConst : ℝ) ^ N * B ^ N :=
            mul_le_mul_of_nonneg_right hCN (pow_pos hBpos N).le
        _ = ((anchorOverlapConst : ℝ) * B) ^ N := (mul_pow _ B N).symm
    calc (s.card : ℝ) ≤ (s'.card : ℝ) * ((anchorOverlapConst : ℝ) * (B ^ N)) := hadiv
      _ = (anchorOverlapConst : ℝ) * (B ^ N) * (s'.card : ℝ) := by ring
      _ ≤ ((anchorOverlapConst : ℝ) * B) ^ N * (s'.card : ℝ) :=
          mul_le_mul_of_nonneg_right hmul (by positivity)
  refine ⟨s', hs'_sub, hcard_final, ⟨?_⟩⟩
  refine LooseUniformTubeSet.ofCoverBrackets
    (s := s') (T := T)
    ({ indexSet := parent'
       assign := cover.assign
       tube := cover.tube
       assign_mem := fun k hk i hi => h_assign'_mem k hk hi
       le_dilate_tube_assign := fun k hk i hi =>
         cover.le_dilate_tube_assign k hk i (hs'_sub hi)
       dir_close_tube_assign := fun k hk i hi =>
         cover.dir_close_tube_assign k hk i (hs'_sub hi)
       nested := fun k hk i hi j hj h =>
         cover.nested k hk i (hs'_sub hi) j (hs'_sub hj) h })
    (fun k => (N₂ k : NNReal)) (C := 2) ?_ ?_ ?_ ?_
  · intro k hk
    exact Set.InjOn.mono (Finset.coe_subset.mpr (h_parent'_sub k hk)) (hinj k hk)
  · intro k hk V
    refine le_trans (Finset.card_le_card ?_) (hbo k hk V)
    intro v hv
    rw [Finset.mem_filter] at hv ⊢
    obtain ⟨hv_par, i, hi_s', hij, hiV⟩ := hv
    exact ⟨h_parent'_sub k hk hv_par, i, hs'_sub hi_s', hij, hiV⟩
  · intro k hk j hj
    have hband := h_band k hk j hj
    have hle : ((Tube.coverClass s' (cover.assign k) j).card : NNReal) ≤ 2 * (N₂ k : NNReal) := by
      have h : (Tube.coverClass s' (cover.assign k) j).card ≤ 2 * N₂ k := by
        simpa [Tube.coverClass] using (le_of_lt hband.2)
      exact_mod_cast h
    exact hle
  · intro k hk j hj
    have hband := h_band k hk j hj
    have hNle : (N₂ k : NNReal) ≤ ((Tube.coverClass s' (cover.assign k) j).card : NNReal) := by
      have h : N₂ k ≤ (Tube.coverClass s' (cover.assign k) j).card := by
        simpa [Tube.coverClass] using hband.1
      exact_mod_cast h
    calc (N₂ k : NNReal) ≤ ((Tube.coverClass s' (cover.assign k) j).card : NNReal) := hNle
      _ ≤ 2 * ((Tube.coverClass s' (cover.assign k) j).card : NNReal) :=
          le_mul_of_one_le_left (by positivity) (by norm_num)


open scoped Classical in
/-- **(3) at GWZ's own grid length**, with the polylogarithmic loss absorbed into `δ^{-α}`. -/
theorem exists_looseUniformTubeSet_subfamily_ssf (K₀ : ℕ) (α : ℝ) (hα : 0 < α) :
    ∃ δ₀ : NNReal, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {ι : Type*} {δ : NNReal}, 0 < δ → δ ≤ δ₀ →
      ∀ (s : Finset ι) (T : ι → Tube δ E3),
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E3) 1) →
      (s.card : ℝ) ≤ (δ : ℝ) ^ (-(K₀ : ℝ)) →
      ∃ s' ⊆ s,
        (s.card : ℝ) ≤ (δ : ℝ) ^ (-α) * (s'.card : ℝ) ∧
        Nonempty (LooseUniformTubeSet s' T (Tube.ssfGridLen δ) 4
          (max 2 (anchorOverlapConst : NNReal))) := by
  classical
  have hC₀one : (1 : ℝ) ≤ (anchorOverlapConst : ℝ) := by
    rw [anchorOverlapConst]; norm_num
  obtain ⟨δ₁, hδ₁pos, hδ₁le1, hthr⟩ :=
    Tube.exists_threshold_polylog_pow_ssfGridLen_le (anchorOverlapConst : ℝ) hC₀one K₀ 1 α hα
  refine ⟨min δ₁ 1, lt_min hδ₁pos (by norm_num), min_le_right _ _, ?_⟩
  intro ι δ hδ hδδ₀ s T hB hscard
  have hδδ₁ : δ ≤ δ₁ := le_trans hδδ₀ (min_le_left _ _)
  have hδ1 : δ ≤ 1 := le_trans hδδ₀ (min_le_right _ _)
  obtain ⟨hNpos, hN16, habs⟩ := hthr hδ hδδ₁
  obtain ⟨s', hs'_sub, hcard, hstruct⟩ :=
    exists_looseUniformTubeSet_subfamily (Tube.ssfGridLen δ) hδ hδ1 hNpos hN16 s T hB
  refine ⟨s', hs'_sub, ?_, hstruct⟩
  set base : ℝ := (anchorOverlapConst : ℝ) * ((⌊Real.logb 2 (s.card : ℝ)⌋₊ : ℝ) + 1) with hbase
  have hbase1 : (1 : ℝ) ≤ base := by
    rw [hbase]
    have hfac : (1 : ℝ) ≤ ((⌊Real.logb 2 (s.card : ℝ)⌋₊ : ℝ) + 1) := by
      have : (0 : ℝ) ≤ (⌊Real.logb 2 (s.card : ℝ)⌋₊ : ℝ) := by positivity
      linarith
    nlinarith
  have habs₁ := habs (s.card : ℝ) (by positivity) hscard
  have hpow : base ^ Tube.ssfGridLen δ ≤ base ^ (1 * Tube.ssfGridLen δ + 1) :=
    pow_le_pow_right₀ hbase1 (by omega)
  calc (s.card : ℝ) ≤ base ^ Tube.ssfGridLen δ * (s'.card : ℝ) := hcard
    _ ≤ base ^ (1 * Tube.ssfGridLen δ + 1) * (s'.card : ℝ) :=
        mul_le_mul_of_nonneg_right hpow (by positivity)
    _ ≤ (δ : ℝ) ^ (-α) * (s'.card : ℝ) :=
        mul_le_mul_of_nonneg_right habs₁ (by positivity)


/-! ### (4) The shaded (Definition 2.2) hierarchy -/

lemma gridScale_one (N k : ℕ) : Tube.gridScale (1 : NNReal) N k = 1 := by
  simp [Tube.gridScale]

/-- Weakening the constant of a loose Definition-2.1 datum. -/
def LooseUniformTubeSet.mono {ι : Type*} {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E3}
    {N : ℕ} {K : ℝ} {C C' : NNReal} (𝒰 : LooseUniformTubeSet s T N K C) (hC : C ≤ C') :
    LooseUniformTubeSet s T N K C' where
  cover := 𝒰.cover
  branchingN := 𝒰.branchingN
  tube_injOn := 𝒰.tube_injOn
  boundedOverlapDil k hk V := (𝒰.boundedOverlapDil k hk V).trans hC
  card_class_le k hk j hj := (𝒰.card_class_le k hk j hj).trans (mul_le_mul' hC le_rfl)
  le_card_class k hk j hj := (𝒰.le_card_class k hk j hj).trans (mul_le_mul' hC le_rfl)

/-- **The dummy exact cover system carrying a loose assignment.**
`ShadedTube.exists_balanced_shadeRefinement_of_cover` reads only `𝒢.assign`, over an *arbitrary*
tube family at an *arbitrary* thickness; this is that family, taken constant at thickness `1`, so
that a loose hierarchy can drive the shaded band step. -/
noncomputable def trivialGridCover {ι : Type*} (s : Finset ι) (N : ℕ)
    {u : E3} (hu : ‖u‖ = 1)
    (indexSet : ℕ → Finset ι) (assign : ℕ → ι → ι)
    (h_assign_mem : ∀ k, k ≤ N → ∀ i ∈ s, assign k i ∈ indexSet k)
    (h_nested : ∀ k, k + 1 ≤ N → ∀ i ∈ s, ∀ j ∈ s,
      assign (k + 1) i = assign (k + 1) j → assign k i = assign k j) :
    Tube.GridCoverSystem s (fun _ : ι => Tube.ofMidpointDirection (1 : NNReal) 0 u hu) N where
  indexSet := indexSet
  assign := assign
  tube := fun k _ => Tube.ofMidpointDirection (Tube.gridScale (1 : NNReal) N k) 0 u hu
  assign_mem := h_assign_mem
  le_tube_assign := by
    intro k hk i hi
    rw [gridScale_one]
  nested := h_nested
  tube_nested := by
    intro k hk i hi
    rw [gridScale_one, gridScale_one]

/-- The `fullness'` form of a shade-mass bound (the private
`ShadedTube.fullness_le_of_shade_sum`, restated here because it is private). -/
theorem fullness_le_of_shade_sum' {ι : Type*} {δ : NNReal} {s : Finset ι} (c : ENNReal)
    (V V' : ι → ShadedTube δ E3) (htube : ∀ i, (V' i).toTube = (V i).toTube)
    (hnum : (∑ i ∈ s, volume (V i).shade) ≤ c * (∑ i ∈ s, volume (V' i).shade)) :
    ShadedBody.fullness' s (fun i => (V i).toShadedBody)
      ≤ c * ShadedBody.fullness' s (fun i => (V' i).toShadedBody) := by
  classical
  change (∑ i ∈ s, volume (V i).shade) / (∑ i ∈ s, volume (V i).carrier)
      ≤ c * ((∑ i ∈ s, volume (V' i).shade) / (∑ i ∈ s, volume (V' i).carrier))
  have hden : (∑ i ∈ s, volume (V i).carrier) = ∑ i ∈ s, volume (V' i).carrier := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    congr 1
    calc (V i).carrier = (V i).toTube.carrier := rfl
      _ = (V' i).toTube.carrier := by rw [← htube i]
      _ = (V' i).carrier := rfl
  calc (∑ i ∈ s, volume (V i).shade) / (∑ i ∈ s, volume (V i).carrier)
      ≤ (c * (∑ i ∈ s, volume (V' i).shade)) / (∑ i ∈ s, volume (V i).carrier) :=
        ENNReal.div_le_div_right hnum _
    _ = c * ((∑ i ∈ s, volume (V' i).shade) / (∑ i ∈ s, volume (V i).carrier)) :=
        mul_div_assoc _ _ _
    _ = c * ((∑ i ∈ s, volume (V' i).shade) / (∑ i ∈ s, volume (V' i).carrier)) := by rw [hden]

open scoped Classical in
/-- **(4) GWZ Definition 2.2 in the loose model, on a subfamily.** -/
theorem exists_looseShadedUniformTubeSet_subfamily {ι : Type*} {δ : NNReal} (N : ℕ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hN : 0 < N)
    (hδ0 : δ ≤ (16 : NNReal) ^ (-(N : ℝ)))
    (s : Finset ι) (V : ι → ShadedTube δ E3)
    (hB : ∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall (0 : E3) 1) :
    ∃ s' ⊆ s, ∃ V' : ι → ShadedTube δ E3,
      (∀ i, (V' i).toTube = (V i).toTube) ∧
      (∀ i, (V' i).shade ⊆ (V i).shade) ∧
      (s.card : ℝ)
          ≤ ((anchorOverlapConst : ℝ) * ((⌊Real.logb 2 (s.card : ℝ)⌋₊ : ℝ) + 1)) ^ N
            * (s'.card : ℝ) ∧
      ShadedBody.fullness' s' (fun i => (V i).toShadedBody)
          ≤ ENNReal.ofReal
              (((anchorOverlapConst : ℝ) * ((⌊Real.logb 2 (s.card : ℝ)⌋₊ : ℝ) + 1)) ^ (2 * N + 2))
            * ShadedBody.fullness' s' (fun i => (V' i).toShadedBody) ∧
      Nonempty (LooseShadedUniformTubeSet s' V' N 4
        (max 4 (max 2 (anchorOverlapConst : NNReal)))) := by
  classical
  obtain ⟨v₀, hv₀ne⟩ := exists_ne (0 : E3)
  have hu₀ : ‖(‖v₀‖⁻¹ • v₀ : E3)‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv₀ne)]
  have hBt : ∀ i ∈ s, ((V i).toTube).carrier ⊆ Metric.closedBall (0 : E3) 1 := by
    intro i hi; simpa using hB i hi
  obtain ⟨s', hs'_sub, hcard, hu⟩ :=
    exists_looseUniformTubeSet_subfamily N hδ hδ1 hN hδ0 s (fun i => (V i).toTube) hBt
  set 𝒰₀ := hu.some with h𝒰₀
  set clamp : ℕ := Nat.log 2 s.card with hclamp_def
  have hclamp : ∀ t : Finset ι, t ⊆ s' → Nat.log 2 t.card ≤ clamp := by
    intro t ht
    exact Nat.log_mono_right (Finset.card_le_card (ht.trans hs'_sub))
  set 𝒢 : Tube.GridCoverSystem s'
      (fun _ : ι => Tube.ofMidpointDirection (1 : NNReal) 0 _ hu₀) N :=
    trivialGridCover s' N hu₀ 𝒰₀.cover.indexSet 𝒰₀.cover.assign
      𝒰₀.cover.assign_mem 𝒰₀.cover.nested with h𝒢
  obtain ⟨Pstar, V', hVto, hVshade, hband, hsum⟩ :=
    ShadedTube.exists_balanced_shadeRefinement_of_cover (V := V) 𝒢 hN clamp hclamp
  have hVto' : (fun i => (V' i).toTube) = (fun i => (V i).toTube) := funext hVto
  have hass : 𝒢.assign = 𝒰₀.cover.assign := rfl
  refine ⟨s', hs'_sub, V', hVto, hVshade, hcard, ?_, ⟨?_⟩⟩
  · refine le_trans (fullness_le_of_shade_sum' _ V V' hVto hsum) ?_
    refine mul_le_mul' ?_ le_rfl
    have hfl : (⌊Real.logb 2 (s.card : ℝ)⌋₊ : ℕ) = Nat.log 2 s.card := by
      exact_mod_cast (Real.natFloor_logb_natCast 2 s.card)
    have hCone : (1 : ℝ) ≤ (anchorOverlapConst : ℝ) := by rw [anchorOverlapConst]; norm_num
    have hBnn : (0 : ℝ) ≤ ((⌊Real.logb 2 (s.card : ℝ)⌋₊ : ℝ) + 1) := by positivity
    have hstep : ((clamp + 1 : ℕ) : ℝ)
        ≤ (anchorOverlapConst : ℝ) * ((⌊Real.logb 2 (s.card : ℝ)⌋₊ : ℝ) + 1) := by
      rw [hclamp_def, ← hfl]
      push_cast
      nlinarith
    have hpow : ((clamp + 1 : ℕ) : ℝ) ^ (2 * N + 2)
        ≤ ((anchorOverlapConst : ℝ) * ((⌊Real.logb 2 (s.card : ℝ)⌋₊ : ℝ) + 1)) ^ (2 * N + 2) :=
      pow_le_pow_left₀ (by positivity) hstep _
    calc ((clamp + 1 : ℕ) : ENNReal) ^ (2 * N + 2)
        = ENNReal.ofReal (((clamp + 1 : ℕ) : ℝ) ^ (2 * N + 2)) := by
          rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal
            (((anchorOverlapConst : ℝ) * ((⌊Real.logb 2 (s.card : ℝ)⌋₊ : ℝ) + 1)) ^ (2 * N + 2)) :=
          ENNReal.ofReal_le_ofReal hpow
  · have h4 : (4 : NNReal) ≤ max 4 (max 2 (anchorOverlapConst : NNReal)) := le_max_left _ _
    have h1 : (1 : NNReal) ≤ max 4 (max 2 (anchorOverlapConst : NNReal)) :=
      le_trans (by norm_num) h4
    have hCle : (max 2 (anchorOverlapConst : NNReal))
        ≤ max 4 (max 2 (anchorOverlapConst : NNReal)) := le_max_right _ _
    exact
      { tubeUniform :=
          { cover :=
              { indexSet := 𝒰₀.cover.indexSet
                assign := 𝒰₀.cover.assign
                tube := 𝒰₀.cover.tube
                assign_mem := 𝒰₀.cover.assign_mem
                le_dilate_tube_assign := by
                  intro k hk i hi
                  simpa [hVto i] using 𝒰₀.cover.le_dilate_tube_assign k hk i hi
                dir_close_tube_assign := by
                  intro k hk i hi
                  simpa [hVto i] using 𝒰₀.cover.dir_close_tube_assign k hk i hi
                nested := 𝒰₀.cover.nested }
            branchingN := 𝒰₀.branchingN
            tube_injOn := 𝒰₀.tube_injOn
            boundedOverlapDil := by
              intro k hk W
              simpa [hVto] using (𝒰₀.boundedOverlapDil k hk W).trans hCle
            card_class_le := fun k hk j hj =>
              (𝒰₀.card_class_le k hk j hj).trans (mul_le_mul' hCle le_rfl)
            le_card_class := fun k hk j hj =>
              (𝒰₀.le_card_class k hk j hj).trans (mul_le_mul' hCle le_rfl) }
        branchingN := fun k => (2 : NNReal) ^ Pstar k
        localN := fun _ k => (2 : NNReal) ^ Pstar k
        card_shadeClass_le := by
          intro x hx k hk i hi hxi
          have hb := (hband x hx k hk i hi hxi).2
          have hle : ((ShadedTube.shadeClass s' V' (𝒢.assign k) (𝒢.assign k i) x).card : NNReal)
              ≤ 4 * (2 : NNReal) ^ Pstar k := by
            have h : (ShadedTube.shadeClass s' V' (𝒢.assign k) (𝒢.assign k i) x).card
                ≤ 4 * 2 ^ Pstar k := le_of_lt hb
            exact_mod_cast h
          exact le_trans hle (mul_le_mul' h4 le_rfl)
        le_card_shadeClass := by
          intro x hx k hk i hi hxi
          have hb := (hband x hx k hk i hi hxi).1
          have hle : (2 : NNReal) ^ Pstar k
              ≤ ((ShadedTube.shadeClass s' V' (𝒢.assign k) (𝒢.assign k i) x).card : NNReal) := by
            exact_mod_cast hb
          calc (2 : NNReal) ^ Pstar k
              ≤ ((ShadedTube.shadeClass s' V' (𝒢.assign k) (𝒢.assign k i) x).card : NNReal) := hle
            _ = 1 * ((ShadedTube.shadeClass s' V' (𝒢.assign k) (𝒢.assign k i) x).card : NNReal) :=
                (one_mul _).symm
            _ ≤ max 4 (max 2 (anchorOverlapConst : NNReal))
                * ((ShadedTube.shadeClass s' V' (𝒢.assign k) (𝒢.assign k i) x).card : NNReal) :=
                mul_le_mul' h1 le_rfl
        branchingN_le := by
          intro x hx k hk
          calc (2 : NNReal) ^ Pstar k = 1 * (2 : NNReal) ^ Pstar k := (one_mul _).symm
            _ ≤ max 4 (max 2 (anchorOverlapConst : NNReal)) * (2 : NNReal) ^ Pstar k :=
                mul_le_mul' h1 le_rfl
        le_branchingN := by
          intro x hx k hk
          calc (2 : NNReal) ^ Pstar k = 1 * (2 : NNReal) ^ Pstar k := (one_mul _).symm
            _ ≤ max 4 (max 2 (anchorOverlapConst : NNReal)) * (2 : NNReal) ^ Pstar k :=
                mul_le_mul' h1 le_rfl }


open scoped Classical in
/-- **(4) at GWZ's own grid length**, both losses absorbed into prescribed powers of `δ`. -/
theorem exists_looseShadedUniformTubeSet_subfamily_ssf (K₀ : ℕ) (α α' : ℝ)
    (hα : 0 < α) (hα' : 0 < α') :
    ∃ δ₀ : NNReal, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {ι : Type*} {δ : NNReal}, 0 < δ → δ ≤ δ₀ →
      ∀ (s : Finset ι) (V : ι → ShadedTube δ E3),
      (∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall (0 : E3) 1) →
      (s.card : ℝ) ≤ (δ : ℝ) ^ (-(K₀ : ℝ)) →
      ∃ s' ⊆ s, ∃ V' : ι → ShadedTube δ E3,
        (∀ i, (V' i).toTube = (V i).toTube) ∧
        (∀ i, (V' i).shade ⊆ (V i).shade) ∧
        (s.card : ℝ) ≤ (δ : ℝ) ^ (-α) * (s'.card : ℝ) ∧
        ShadedBody.fullness' s' (fun i => (V i).toShadedBody)
            ≤ ENNReal.ofReal ((δ : ℝ) ^ (-α'))
              * ShadedBody.fullness' s' (fun i => (V' i).toShadedBody) ∧
        Nonempty (LooseShadedUniformTubeSet s' V' (Tube.ssfGridLen δ) 4
          (max 4 (max 2 (anchorOverlapConst : NNReal)))) := by
  classical
  have hC₀one : (1 : ℝ) ≤ (anchorOverlapConst : ℝ) := by
    rw [anchorOverlapConst]; norm_num
  obtain ⟨δ₁, hδ₁pos, hδ₁le1, hthr₁⟩ :=
    Tube.exists_threshold_polylog_pow_ssfGridLen_le (anchorOverlapConst : ℝ) hC₀one K₀ 1 α hα
  obtain ⟨δ₂, hδ₂pos, hδ₂le1, hthr₂⟩ :=
    Tube.exists_threshold_polylog_pow_ssfGridLen_le (anchorOverlapConst : ℝ) hC₀one K₀ 2 α' hα'
  refine ⟨min (min δ₁ δ₂) 1, lt_min (lt_min hδ₁pos hδ₂pos) (by norm_num),
    min_le_right _ _, ?_⟩
  intro ι δ hδ hδδ₀ s V hB hscard
  have hδδ₁ : δ ≤ δ₁ := le_trans hδδ₀ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hδδ₂ : δ ≤ δ₂ := le_trans hδδ₀ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hδ1 : δ ≤ 1 := le_trans hδδ₀ (min_le_right _ _)
  obtain ⟨hNpos, hN16, habs₁⟩ := hthr₁ hδ hδδ₁
  obtain ⟨-, -, habs₂⟩ := hthr₂ hδ hδδ₂
  obtain ⟨s', hs'_sub, V', hVto, hVshade, hcard, hfull, hstruct⟩ :=
    exists_looseShadedUniformTubeSet_subfamily (Tube.ssfGridLen δ) hδ hδ1 hNpos hN16 s V hB
  set base : ℝ := (anchorOverlapConst : ℝ) * ((⌊Real.logb 2 (s.card : ℝ)⌋₊ : ℝ) + 1) with hbase
  have hbase1 : (1 : ℝ) ≤ base := by
    rw [hbase]
    have : (0 : ℝ) ≤ (⌊Real.logb 2 (s.card : ℝ)⌋₊ : ℝ) := by positivity
    nlinarith
  refine ⟨s', hs'_sub, V', hVto, hVshade, ?_, ?_, hstruct⟩
  · have h1 := habs₁ (s.card : ℝ) (by positivity) hscard
    have hpow : base ^ Tube.ssfGridLen δ ≤ base ^ (1 * Tube.ssfGridLen δ + 1) :=
      pow_le_pow_right₀ hbase1 (by omega)
    calc (s.card : ℝ) ≤ base ^ Tube.ssfGridLen δ * (s'.card : ℝ) := hcard
      _ ≤ base ^ (1 * Tube.ssfGridLen δ + 1) * (s'.card : ℝ) :=
          mul_le_mul_of_nonneg_right hpow (by positivity)
      _ ≤ (δ : ℝ) ^ (-α) * (s'.card : ℝ) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
  · have h2 := habs₂ (s.card : ℝ) (by positivity) hscard
    refine le_trans hfull (mul_le_mul' ?_ le_rfl)
    refine ENNReal.ofReal_le_ofReal ?_
    calc base ^ (2 * Tube.ssfGridLen δ + 2)
        ≤ (δ : ℝ) ^ (-α') := h2


/-- Weakening the constant of a loose Definition-2.2 datum. -/
def LooseShadedUniformTubeSet.mono {ι : Type*} {δ : NNReal} {s : Finset ι}
    {V : ι → ShadedTube δ E3} {N : ℕ} {K : ℝ} {C C' : NNReal}
    (𝒱 : LooseShadedUniformTubeSet s V N K C) (hC : C ≤ C') :
    LooseShadedUniformTubeSet s V N K C' where
  tubeUniform := 𝒱.tubeUniform.mono hC
  branchingN := 𝒱.branchingN
  localN := 𝒱.localN
  card_shadeClass_le := fun x hx k hk i hi hxi =>
    (𝒱.card_shadeClass_le x hx k hk i hi hxi).trans (mul_le_mul' hC le_rfl)
  le_card_shadeClass := fun x hx k hk i hi hxi =>
    (𝒱.le_card_shadeClass x hx k hk i hi hxi).trans (mul_le_mul' hC le_rfl)
  branchingN_le := fun x hx k hk => (𝒱.branchingN_le x hx k hk).trans (mul_le_mul' hC le_rfl)
  le_branchingN := fun x hx k hk => (𝒱.le_branchingN x hx k hk).trans (mul_le_mul' hC le_rfl)

theorem four_le_anchorOverlapConst : (4 : NNReal) ≤ (anchorOverlapConst : NNReal) := by
  have h : (4 : ℕ) ≤ anchorOverlapConst := by rw [anchorOverlapConst]; norm_num
  exact_mod_cast h

theorem two_le_anchorOverlapConst : (2 : NNReal) ≤ (anchorOverlapConst : NNReal) :=
  le_trans (by norm_num) four_le_anchorOverlapConst

open scoped Classical in
/-- **The plug for conjunct 6's `∃ 𝒱`, at the configuration.** -/
theorem exists_looseShaded_subfamily_of_config (K₀ : ℕ) (α α' : ℝ) (hα : 0 < α) (hα' : 0 < α') :
    ∃ δ₀ : NNReal, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ (cfg : Kakeya.VeryNotSticky), cfg.δ ≤ δ₀ →
        (cfg.s.card : ℝ) ≤ (cfg.δ : ℝ) ^ (-(K₀ : ℝ)) →
      ∃ s' ⊆ cfg.s, ∃ V' : cfg.ι → ShadedTube cfg.δ E3,
        (∀ i, (V' i).toTube = (cfg.T i).toTube) ∧
        (∀ i, (V' i).shade ⊆ (cfg.T i).shade) ∧
        (cfg.s.card : ℝ) ≤ (cfg.δ : ℝ) ^ (-α) * (s'.card : ℝ) ∧
        ShadedBody.fullness' s' (fun i => (cfg.T i).toShadedBody)
            ≤ ENNReal.ofReal ((cfg.δ : ℝ) ^ (-α'))
              * ShadedBody.fullness' s' (fun i => (V' i).toShadedBody) ∧
        Nonempty (LooseShadedUniformTubeSet s' V' (Tube.ssfGridLen cfg.δ) 4
          (max cfg.C₀ (anchorOverlapConst : NNReal))) := by
  classical
  obtain ⟨δ₀, hδ₀pos, hδ₀le1, hmain⟩ :=
    exists_looseShadedUniformTubeSet_subfamily_ssf K₀ α α' hα hα'
  refine ⟨δ₀, hδ₀pos, hδ₀le1, ?_⟩
  intro cfg hδ hscard
  obtain ⟨s', hs'_sub, V', hVto, hVshade, hcard, hfull, hstruct⟩ :=
    hmain cfg.hδ hδ cfg.s cfg.T (fun i hi => cfg.contained i hi) hscard
  refine ⟨s', hs'_sub, V', hVto, hVshade, hcard, hfull, ⟨?_⟩⟩
  refine hstruct.some.mono ?_
  have hle : max 4 (max 2 (anchorOverlapConst : NNReal)) = (anchorOverlapConst : NNReal) := by
    rw [max_eq_right two_le_anchorOverlapConst, max_eq_right four_le_anchorOverlapConst]
  rw [hle]
  exact le_max_right _ _


end LooseUniform
end Kakeya

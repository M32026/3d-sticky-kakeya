/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.TubeParentPacking
public import Kakeya.DimensionThree.BoundedOverlapCount

/-!
# Helpers for a hybrid `ρ`-parent producer

The coarse parent system of `Kakeya/DimensionThree/Plank/TubeParentPacking.lean` is built over the
concrete ambient `EuclideanSpace ℝ (Fin 3)` and, at the counting step, over a `MeasureSpace`
instance carrying an additive Haar measure.  A hybrid producer that has to run inside an abstract
three-dimensional inner-product space cannot cite it directly.  This file restates the four
ingredients it needs, each over the weakest hypotheses the argument actually uses.

* **Mixed radii.**  `Kakeya.Tube.carrier_subset_rescale_of_center_dir_close_mixed` is
  `Kakeya.Tube.carrier_subset_rescale_of_center_dir_close` with the two tubes allowed different
  radii.  The containing tube's radius never enters that proof — only its centre, direction,
  endpoints, and rescale do — and both endgames
  (`Kakeya.Tube.carrier_subset_of_endpoints_close` and its `_flip`) are mixed-radius already.
* **Rescale inside a dilate.**  `Kakeya.Tube.rescale_le_dilate_of_le_mul` puts the `s`-rescale of a
  `ρ`-tube inside its `C`-dilate as soon as `s ≤ C ρ` and `1 ≤ C`; the concentric case of
  `Kakeya.ml1Boot.rescale_le_dilate_two`, with the ratio left free.
* **Abstract-`E` separated assignment.**  `Kakeya.exists_separatedAssignment_abstract` is
  `Kakeya.exists_separatedAssignment` over an arbitrary normed space, its proof using only
  `Kakeya.exists_max_card_separated` and the two formal facts `Kakeya.tubeParamDist_comm` and
  `Kakeya.tubeParamDist_self`.  The assignment fixes the selected leaves
  (`Kakeya.assign_eq_self_of_mem_separated`), hence is onto them
  (`Kakeya.surjOn_assign_of_mem_separated`).
* **The `ρ ^ (-5)` packing count.**  `Kakeya.card_le_of_tubeParamDist_separated_of_finrank_three`
  bounds a `ρ/8`-separated family of tubes with carriers in `B̄(0,1)`.  It does *not* go through
  `Kakeya.card_le_of_tubeParamDist_separated`, whose packing engine
  `Kakeya.card_le_of_separated_in_ball` needs a `MeasureSpace` instance and an additive Haar
  measure.  Instead it fibres over a maximal `ρ/16`-separated set of centres and uses the
  abstract-`E` pair `Kakeya.ml1Boot.card_le_of_ball_separated` (centres, `ρ ^ (-3)`) and
  `Kakeya.ml1Boot.card_le_of_unit_separated` (directions, `ρ ^ (-2)`).  The exponent `5 = 3 + 2`
  is exactly this split, and it is why `Kakeya.tubeParamDist` is a `max`: two members of one fibre
  have centres within `ρ/8`, so their *directions* must carry the separation.
-/

@[expose] public section

open MeasureTheory Metric Set Convexity ConvexSpaceBody

open scoped NNReal ENNReal

noncomputable section

namespace Kakeya

/-! ### Mixed-radius containment -/

/-- **Mixed-radius form of `Kakeya.Tube.carrier_subset_rescale_of_center_dir_close`.**

A `δ₁`-tube whose centre is within `c` of a `δ₂`-tube's centre and whose direction agrees with the
latter's within `c` up to sign lies in the `s`-rescale of the second tube whenever
`δ₁ + 3c/2 ≤ s`.  The radius `δ₂` is irrelevant: the second tube enters only through its centre,
direction, endpoints and its rescale to radius `s`. -/
theorem Tube.carrier_subset_rescale_of_center_dir_close_mixed
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {δ₁ δ₂ : ℝ≥0} (T₁ : Tube δ₁ E) (T₂ : Tube δ₂ E) {c : ℝ} (hc0 : 0 ≤ c)
    (hm : dist T₁.center T₂.center ≤ c)
    (hd : min ‖T₁.direction - T₂.direction‖ ‖T₁.direction + T₂.direction‖ ≤ c)
    {s : ℝ≥0} (hs : (δ₁ : ℝ) + 3 * c / 2 ≤ (s : ℝ)) :
    (T₁.carrier : Set E) ⊆ ((T₂.rescale s).carrier : Set E) := by
  have hmc : ‖T₁.center - T₂.center‖ ≤ c := by
    simpa [dist_eq_norm] using hm
  rcases min_le_iff.mp hd with hd₁ | hd₂
  · -- aligned directions
    have hbd : ‖(2⁻¹ : ℝ) • (T₁.direction - T₂.direction)‖ ≤ c / 2 := by
      calc
        ‖(2⁻¹ : ℝ) • (T₁.direction - T₂.direction)‖
            ≤ ‖(2⁻¹ : ℝ)‖ * ‖T₁.direction - T₂.direction‖ := norm_smul_le _ _
        _ = (1 / 2 : ℝ) * ‖T₁.direction - T₂.direction‖ := by
            norm_num
        _ ≤ c / 2 := by
            nlinarith [hd₁, hc0]
    have hxx : dist T₁.x T₂.x ≤ 3 * c / 2 := by
      rw [dist_eq_norm, Tube.x_eq_center_sub T₁, Tube.x_eq_center_sub T₂]
      rw [show T₁.center - (2⁻¹ : ℝ) • T₁.direction - (T₂.center - (2⁻¹ : ℝ) • T₂.direction)
          = (T₁.center - T₂.center) - (2⁻¹ : ℝ) • (T₁.direction - T₂.direction) by module]
      calc
        ‖(T₁.center - T₂.center) - (2⁻¹ : ℝ) • (T₁.direction - T₂.direction)‖
            ≤ ‖T₁.center - T₂.center‖ + ‖(2⁻¹ : ℝ) • (T₁.direction - T₂.direction)‖ :=
              norm_sub_le _ _
        _ ≤ c + c / 2 := by
              exact add_le_add hmc hbd
        _ = 3 * c / 2 := by ring
    have hyy : dist T₁.y T₂.y ≤ 3 * c / 2 := by
      rw [dist_eq_norm, Tube.y_eq_center_add T₁, Tube.y_eq_center_add T₂]
      rw [show T₁.center + (2⁻¹ : ℝ) • T₁.direction - (T₂.center + (2⁻¹ : ℝ) • T₂.direction)
          = (T₁.center - T₂.center) + (2⁻¹ : ℝ) • (T₁.direction - T₂.direction) by module]
      calc
        ‖(T₁.center - T₂.center) + (2⁻¹ : ℝ) • (T₁.direction - T₂.direction)‖
            ≤ ‖T₁.center - T₂.center‖ + ‖(2⁻¹ : ℝ) • (T₁.direction - T₂.direction)‖ :=
              norm_add_le _ _
        _ ≤ c + c / 2 := by
              exact add_le_add hmc hbd
        _ = 3 * c / 2 := by ring
    exact Tube.carrier_subset_of_endpoints_close (T := T₁) (V := T₂.rescale s)
      (r := 3 * c / 2)
      (show dist T₁.x (T₂.rescale s).x ≤ 3 * c / 2 by simpa [Tube.rescale] using hxx)
      (show dist T₁.y (T₂.rescale s).y ≤ 3 * c / 2 by simpa [Tube.rescale] using hyy)
      hs
  · -- anti-aligned : ‖T₁.direction + T₂.direction‖ ≤ c
    have hbd : ‖(2⁻¹ : ℝ) • (T₁.direction + T₂.direction)‖ ≤ c / 2 := by
      calc
        ‖(2⁻¹ : ℝ) • (T₁.direction + T₂.direction)‖
            ≤ ‖(2⁻¹ : ℝ)‖ * ‖T₁.direction + T₂.direction‖ := norm_smul_le _ _
        _ = (1 / 2 : ℝ) * ‖T₁.direction + T₂.direction‖ := by
            norm_num
        _ ≤ c / 2 := by
            nlinarith [hd₂, hc0]
    have hxy : dist T₁.x T₂.y ≤ 3 * c / 2 := by
      rw [dist_eq_norm, Tube.x_eq_center_sub T₁, Tube.y_eq_center_add T₂]
      rw [show T₁.center - (2⁻¹ : ℝ) • T₁.direction - (T₂.center + (2⁻¹ : ℝ) • T₂.direction)
          = (T₁.center - T₂.center) - (2⁻¹ : ℝ) • (T₁.direction + T₂.direction) by module]
      calc
        ‖(T₁.center - T₂.center) - (2⁻¹ : ℝ) • (T₁.direction + T₂.direction)‖
            ≤ ‖T₁.center - T₂.center‖ + ‖(2⁻¹ : ℝ) • (T₁.direction + T₂.direction)‖ :=
              norm_sub_le _ _
        _ ≤ c + c / 2 := by
              exact add_le_add hmc hbd
        _ = 3 * c / 2 := by ring
    have hyx : dist T₁.y T₂.x ≤ 3 * c / 2 := by
      rw [dist_eq_norm, Tube.y_eq_center_add T₁, Tube.x_eq_center_sub T₂]
      rw [show T₁.center + (2⁻¹ : ℝ) • T₁.direction - (T₂.center - (2⁻¹ : ℝ) • T₂.direction)
          = (T₁.center - T₂.center) + (2⁻¹ : ℝ) • (T₁.direction + T₂.direction) by module]
      calc
        ‖(T₁.center - T₂.center) + (2⁻¹ : ℝ) • (T₁.direction + T₂.direction)‖
            ≤ ‖T₁.center - T₂.center‖ + ‖(2⁻¹ : ℝ) • (T₁.direction + T₂.direction)‖ :=
              norm_add_le _ _
        _ ≤ c + c / 2 := by
              exact add_le_add hmc hbd
        _ = 3 * c / 2 := by ring
    exact Tube.carrier_subset_of_endpoints_close_flip (T := T₁) (V := T₂.rescale s)
      (c := 3 * c / 2)
      (show dist T₁.x (T₂.rescale s).y ≤ 3 * c / 2 by simpa [Tube.rescale] using hxy)
      (show dist T₁.y (T₂.rescale s).x ≤ 3 * c / 2 by simpa [Tube.rescale] using hyx)
      hs

/-! ### A rescale inside a dilate -/

/-- **A rescale of a tube sits inside a dilate of it.**

For `1 ≤ C` and `s ≤ C ρ`, the `s`-rescale of a `ρ`-tube `T` lies in the `C`-dilate of `T`: every
point of the rescale is within `s ≤ Cρ` of a point of the core, and every core point is
`T.center + u • T.direction` with `|u| ≤ 1/2 ≤ C/2`, which is exactly the hypothesis of
`Kakeya.Tube.mem_dilate_of_dist_axis_le`. -/
theorem Tube.rescale_le_dilate_of_le_mul
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {ρ s : ℝ≥0} (T : Tube ρ E) {C : ℝ} (hC : 1 ≤ C) (hs : (s : ℝ) ≤ C * (ρ : ℝ)) :
    (T.rescale s).toConvexSpaceBody ≤ Kakeya.Tube.dilate T C := by
  intro z hz
  change z ∈ (T.rescale s).carrier at hz
  have hxσ : (T.rescale s).x = T.x := by simp [Tube.rescale]
  have hyσ : (T.rescale s).y = T.y := by simp [Tube.rescale]
  rw [(T.rescale s).carrier_eq] at hz
  rw [Set.mem_iUnion₂] at hz
  rw [hxσ, hyσ] at hz
  obtain ⟨p, hp_seg, h_zp⟩ := hz
  rw [Metric.mem_closedBall] at h_zp
  rw [segment_eq_image'] at hp_seg
  obtain ⟨u, hu, hp_eq⟩ := hp_seg
  let t : ℝ := u - 1 / 2
  have hpt : p = T.center + t • T.direction := by
    rw [← hp_eq]
    dsimp [t]
    have hc : T.center = (1 / 2 : ℝ) • (T.x + T.y) := by
      change midpoint ℝ T.x T.y = (1 / 2 : ℝ) • (T.x + T.y)
      rw [midpoint_eq_smul_add]
      norm_num
    rw [hc]
    module
  have ht : |t| ≤ C / 2 := by
    have ht12 : |t| ≤ 1 / 2 := by
      dsimp [t]
      rw [abs_le]
      constructor <;> linarith [hu.1, hu.2]
    have hChalf : (1 / 2 : ℝ) ≤ C / 2 := by linarith
    exact ht12.trans hChalf
  have hz2 : dist z (T.center + t • T.direction) ≤ C * (ρ : ℝ) := by
    rw [← hpt]
    calc
      dist z p ≤ (s : ℝ) := h_zp
      _ ≤ C * (ρ : ℝ) := hs
  exact Tube.mem_dilate_of_dist_axis_le (T := T) (C := C)
    (hC := (by linarith : (0 : ℝ) < C)) (s := t) (hs := ht) (hz := hz2)

/-! ### The separated assignment over an abstract ambient space -/

/-- **Abstract-`E` form of `Kakeya.exists_separatedAssignment`.**

A maximum-cardinality `ρ/8`-separated subfamily of the leaves, together with a map sending each
leaf to a selected leaf within parameter distance `ρ/8`.  The ambient space is an arbitrary normed
space: the proof uses only `Kakeya.exists_max_card_separated`, `Kakeya.tubeParamDist_comm` and
`Kakeya.tubeParamDist_self`. -/
theorem exists_separatedAssignment_abstract
    {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {δ ρ : ℝ≥0} (hρ0 : 0 < ρ) (q : Finset ι) (hq : q.Nonempty) (T : ι → Tube δ E) :
    ∃ (S : Finset ι) (assign : ι → ι),
      S ⊆ q ∧
      (∀ i ∈ S, ∀ j ∈ S, i ≠ j → (ρ : ℝ) / 8 < tubeParamDist (T i) (T j)) ∧
      (∀ i ∈ q, assign i ∈ S) ∧
      (∀ i ∈ q, tubeParamDist (T (assign i)) (T i) ≤ (ρ : ℝ) / 8) := by
  classical
  obtain ⟨i₀, hi₀⟩ := hq
  have hρ0' : (0 : ℝ) < (ρ : ℝ) := by exact_mod_cast hρ0
  have hsep0 : (0 : ℝ) < (ρ : ℝ) / 8 := by linarith
  let Rel : ι → ι → Prop := fun i j => (ρ : ℝ) / 8 < tubeParamDist (T i) (T j)
  have hsymm : ∀ i j, Rel i j → Rel j i := by
    intro i j h
    simpa [Rel, tubeParamDist_comm] using h
  obtain ⟨S, hSq, hSsep, hSsat⟩ := exists_max_card_separated q Rel hsymm
  have hchoose : ∀ i ∈ q, ∃ k, k ∈ S ∧ tubeParamDist (T k) (T i) ≤ (ρ : ℝ) / 8 := by
    intro i hi
    obtain ⟨k, hkS, hk⟩ := hSsat i hi
    refine ⟨k, hkS, ?_⟩
    rcases hk with rfl | hk
    · rw [tubeParamDist_self]
      exact hsep0.le
    · exact not_lt.mp hk
  let assign : ι → ι := fun i =>
    if h : ∃ k, k ∈ S ∧ tubeParamDist (T k) (T i) ≤ (ρ : ℝ) / 8 then
      h.choose
    else
      i₀
  have hassign : ∀ i ∈ q, assign i ∈ S ∧
      tubeParamDist (T (assign i)) (T i) ≤ (ρ : ℝ) / 8 := by
    intro i hi
    dsimp [assign]
    rw [dif_pos (hchoose i hi)]
    exact (hchoose i hi).choose_spec
  exact ⟨S, assign, hSq, hSsep, fun i hi => (hassign i hi).1, fun i hi => (hassign i hi).2⟩

/-- **A separated assignment fixes the selected leaves.**

If `k` is selected then `assign k` is selected too and lies within parameter distance `ρ/8` of `k`,
while distinct selected leaves are more than `ρ/8` apart; so `assign k = k`. -/
theorem assign_eq_self_of_mem_separated
    {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {δ ρ : ℝ≥0} {q S : Finset ι} {assign : ι → ι} {T : ι → Tube δ E}
    (hSq : S ⊆ q)
    (hSsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → (ρ : ℝ) / 8 < tubeParamDist (T i) (T j))
    (hmem : ∀ i ∈ q, assign i ∈ S)
    (hclose : ∀ i ∈ q, tubeParamDist (T (assign i)) (T i) ≤ (ρ : ℝ) / 8)
    {k : ι} (hk : k ∈ S) : assign k = k := by
  by_contra hne
  have hkq : k ∈ q := hSq hk
  have hakS : assign k ∈ S := hmem k hkq
  have hck : tubeParamDist (T (assign k)) (T k) ≤ (ρ : ℝ) / 8 := hclose k hkq
  have hsep : (ρ : ℝ) / 8 < tubeParamDist (T (assign k)) (T k) :=
    hSsep (assign k) hakS k hk hne
  linarith

/-- **A separated assignment is onto the selected leaves**, immediately from
`Kakeya.assign_eq_self_of_mem_separated`. -/
theorem surjOn_assign_of_mem_separated
    {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {δ ρ : ℝ≥0} {q S : Finset ι} {assign : ι → ι} {T : ι → Tube δ E}
    (hSq : S ⊆ q)
    (hSsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → (ρ : ℝ) / 8 < tubeParamDist (T i) (T j))
    (hmem : ∀ i ∈ q, assign i ∈ S)
    (hclose : ∀ i ∈ q, tubeParamDist (T (assign i)) (T i) ≤ (ρ : ℝ) / 8) :
    Set.SurjOn assign (q : Set ι) (S : Set ι) := by
  intro k hk
  exact ⟨k, hSq hk, assign_eq_self_of_mem_separated hSq hSsep hmem hclose hk⟩

/-! ### The abstract-`E` packing count -/

section Packing

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Direction count.**  A family of tubes with pairwise `η`-separated directions has
`O(η ^ (-2))` members: directions are unit vectors (`Tube.norm_direction`), separation makes the
direction map injective on the family, and `Kakeya.ml1Boot.card_le_of_unit_separated` counts the
image. -/
theorem card_le_of_direction_separated (hdim : Module.finrank ℝ E = 3)
    {δ : ℝ≥0} (T : ι → Tube δ E) (F : Finset ι) {η : ℝ≥0} (hη : 0 < η) (hη1 : η ≤ 1)
    (hsep : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → (η : ℝ) < ‖(T i).direction - (T j).direction‖) :
    (F.card : ℝ≥0∞) ≤ (ml1Boot.dirNet.C : ℝ≥0∞) * (η : ℝ≥0∞)⁻¹ ^ 2 := by
  classical
  let D : Finset E := F.image fun i => (T i).direction
  have hinj : Set.InjOn (fun i => (T i).direction) (F : Set ι) := by
    intro i hi j hj hdir
    have hdir' : (T i).direction = (T j).direction := by simpa using hdir
    by_contra hij
    have hlt := hsep i hi j hj hij
    rw [hdir', sub_self, norm_zero] at hlt
    have hηr : (0 : ℝ) < (η : ℝ) := by exact_mod_cast hη
    linarith
  have hcard : D.card = F.card := by
    dsimp [D]
    exact Finset.card_image_of_injOn hinj
  have hunit : ∀ d ∈ D, ‖d‖ = 1 := by
    intro d hd
    rw [Finset.mem_image] at hd
    rcases hd with ⟨i, hi, rfl⟩
    exact (T i).norm_direction
  have hsepD : ∀ a ∈ D, ∀ b ∈ D, a ≠ b → (η : ℝ) < ‖a - b‖ := by
    intro a ha b hb hab
    rw [Finset.mem_image] at ha hb
    rcases ha with ⟨i, hi, rfl⟩
    rcases hb with ⟨j, hj, rfl⟩
    have hij : i ≠ j := by
      intro hij
      apply hab
      rw [hij]
    exact hsep i hi j hj hij
  have hle : (D.card : ℝ≥0∞) ≤ (ml1Boot.dirNet.C : ℝ≥0∞) * (η : ℝ≥0∞)⁻¹ ^ 2 :=
    ml1Boot.card_le_of_unit_separated hdim hη hη1 hunit hsepD
  simpa [hcard] using hle

/-- **Centre count.**  A family of tubes with carriers in `B̄(0,1)` and pairwise `η`-separated
centres has `O(η ^ (-3))` members, by `Kakeya.ml1Boot.card_le_of_ball_separated`: a tube's centre
lies in its carrier, hence in `B̄(0,1) ⊆ B̄(0,3)`, and separation makes the centre map injective on
the family. -/
theorem card_le_of_center_separated (hdim : Module.finrank ℝ E = 3)
    {δ : ℝ≥0} (T : ι → Tube δ E) (F : Finset ι) {η : ℝ≥0} (hη : 0 < η) (hη1 : η ≤ 1)
    (hball : ∀ i ∈ F, (T i).carrier ⊆ Metric.closedBall (0 : E) 1)
    (hsep : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → (η : ℝ) < dist (T i).center (T j).center) :
    (F.card : ℝ≥0∞) ≤ (ml1Boot.posNet.C : ℝ≥0∞) * (η : ℝ≥0∞)⁻¹ ^ 3 := by
  classical
  let P : Finset E := F.image fun i => (T i).center
  have hinj : Set.InjOn (fun i => (T i).center) (F : Set ι) := by
    intro i hi j hj hc
    have hc' : (T i).center = (T j).center := by simpa using hc
    by_contra hij
    have hlt := hsep i hi j hj hij
    rw [hc', dist_self] at hlt
    have hηr : (0 : ℝ) < (η : ℝ) := by exact_mod_cast hη
    linarith
  have hcard : P.card = F.card := by
    dsimp [P]
    exact Finset.card_image_of_injOn hinj
  have hmem : ∀ p ∈ P, ‖p‖ ≤ 3 := by
    intro p hp
    rw [Finset.mem_image] at hp
    rcases hp with ⟨i, hi, rfl⟩
    have hc : (T i).center ∈ Metric.closedBall (0 : E) 1 :=
      hball i hi (Tube.center_mem_carrier (T := T i))
    have hn : ‖(T i).center‖ ≤ 1 := by
      rw [Metric.mem_closedBall, dist_eq_norm] at hc
      simpa using hc
    linarith
  have hsepP : ∀ a ∈ P, ∀ b ∈ P, a ≠ b → (η : ℝ) < ‖a - b‖ := by
    intro a ha b hb hab
    rw [Finset.mem_image] at ha hb
    rcases ha with ⟨i, hi, rfl⟩
    rcases hb with ⟨j, hj, rfl⟩
    have hij : i ≠ j := by
      intro hij
      apply hab
      rw [hij]
    simpa [dist_eq_norm] using hsep i hi j hj hij
  have hle : (P.card : ℝ≥0∞) ≤ (ml1Boot.posNet.C : ℝ≥0∞) * (η : ℝ≥0∞)⁻¹ ^ 3 :=
    ml1Boot.card_le_of_ball_separated hdim hη hη1 hmem hsepP
  simpa [hcard] using hle

/-- The absolute constant in `Kakeya.card_le_of_tubeParamDist_separated_of_finrank_three`: the
product of the centre-packing constant `Kakeya.ml1Boot.posNet.C` at scale `ρ/16`, the
direction-packing constant `Kakeya.ml1Boot.dirNet.C` at scale `ρ/8`, and the scale conversion
`16 ^ 3 * 8 ^ 2 = 262144`. -/
noncomputable def hybridPackingConst : ℝ≥0 := 262144 * ml1Boot.posNet.C * ml1Boot.dirNet.C

/-- **The abstract-`E` `ρ ^ (-5)` packing count.**

A family of `δ`-tubes with carriers in `B̄(0,1)`, pairwise `ρ/8`-separated in
`Kakeya.tubeParamDist`, has at most `C ρ ^ (-5)` members, over any three-dimensional inner-product
space.

Fibre the family over a maximal `ρ/16`-separated set of centres
(`Kakeya.exists_max_card_separated`).  That set is counted by `Kakeya.card_le_of_center_separated`,
giving `ρ ^ (-3)`.  Two members of one fibre have centres within `ρ/8` of each other, so — since
`Kakeya.tubeParamDist` is a `max` — the separation must be carried by their directions, and
`Kakeya.card_le_of_direction_separated` counts each fibre with `ρ ^ (-2)`.  The exponent is
`5 = 3 + 2`.

Unlike `Kakeya.card_le_of_tubeParamDist_separated` this needs no `MeasureSpace` instance and no
additive Haar measure on `E`. -/
theorem card_le_of_tubeParamDist_separated_of_finrank_three (hdim : Module.finrank ℝ E = 3)
    {δ ρ : ℝ≥0} (T : ι → Tube δ E) (S : Finset ι) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hSsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → (ρ : ℝ) / 8 < tubeParamDist (T i) (T j))
    (hball : ∀ i ∈ S, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) :
    (S.card : ℝ≥0∞) ≤ (hybridPackingConst : ℝ≥0∞) * (ρ : ℝ≥0∞) ^ (-5 : ℝ) := by
  classical
  -- STEP 1: a maximal `ρ/16`-separated set of centres.
  obtain ⟨S', hS'sub, hS'sep, hS'sat⟩ :=
    exists_max_card_separated S (fun i j => (ρ : ℝ) / 16 < dist (T i).center (T j).center)
      (by intro i j h
          rwa [dist_comm])
  have hs_sat : ∀ k ∈ S, ∃ i ∈ S', i = k ∨ dist (T i).center (T k).center ≤ (ρ : ℝ) / 16 := by
    intro k hk
    rcases hS'sat k hk with ⟨i, hi, h⟩
    refine ⟨i, hi, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (not_lt.mp h)
  -- STEP 2: the fibring map (fibres `S` over `S'`).
  let f : ι → ι := fun k =>
    if h : ∃ i ∈ S', (i = k ∨ dist (T i).center (T k).center ≤ (ρ : ℝ) / 16) then Classical.choose h
    else k
  have hf_mem : ∀ k ∈ S, f k ∈ S' := by
    intro k hk
    dsimp [f]
    rw [dif_pos (hs_sat k hk)]
    exact (Classical.choose_spec (hs_sat k hk)).1
  have hf_prop : ∀ k ∈ S, (f k = k ∨ dist (T (f k)).center (T k).center ≤ (ρ : ℝ) / 16) := by
    intro k hk
    dsimp [f]
    rw [dif_pos (hs_sat k hk)]
    exact (Classical.choose_spec (hs_sat k hk)).2
  have hf_dist : ∀ k ∈ S, dist (T (f k)).center (T k).center ≤ (ρ : ℝ) / 16 := by
    intro k hk
    rcases hf_prop k hk with h | h
    · rw [h]
      simpa using show (0 : ℝ) ≤ (ρ : ℝ) / 16 by positivity
    · exact h
  -- STEP 3: bound `S'` by the centre packing.
  have hη₁0 : 0 < ρ / 16 := by positivity
  have hη₁1 : (ρ / 16 : ℝ≥0) ≤ 1 := by
    exact (div_le_self (le_of_lt hρ0) (by norm_num : (1 : ℝ≥0) ≤ 16)).trans hρ1
  have hS'ball : ∀ i ∈ S', (T i).carrier ⊆ Metric.closedBall (0 : E) 1 := by
    intro i hi
    exact hball i (hS'sub hi)
  have hS'center : (S'.card : ℝ≥0∞) ≤ (ml1Boot.posNet.C : ℝ≥0∞) * ((ρ / 16 : ℝ≥0) : ℝ≥0∞)⁻¹ ^ 3 :=
    card_le_of_center_separated hdim T S' (η := ρ / 16) hη₁0 hη₁1 hS'ball hS'sep
  -- STEP 4: bound each fibre by the direction packing.
  have hη₂0 : 0 < ρ / 8 := by positivity
  have hη₂1 : (ρ / 8 : ℝ≥0) ≤ 1 := by
    exact (div_le_self (le_of_lt hρ0) (by norm_num : (1 : ℝ≥0) ≤ 8)).trans hρ1
  have hFib : ∀ b ∈ S', ((S.filter fun a => f a = b).card : ℝ≥0∞) ≤
      (ml1Boot.dirNet.C : ℝ≥0∞) * ((ρ / 8 : ℝ≥0) : ℝ≥0∞)⁻¹ ^ 2 := by
    intro b hb
    let Fb : Finset ι := S.filter fun a => f a = b
    have hFb_memS : ∀ k ∈ Fb, k ∈ S := by
      intro k hk
      exact (Finset.mem_filter.mp hk).1
    have hFb_f : ∀ k ∈ Fb, f k = b := by
      intro k hk
      exact (Finset.mem_filter.mp hk).2
    have hFb_center : ∀ k ∈ Fb, dist (T b).center (T k).center ≤ (ρ : ℝ) / 16 := by
      intro k hk
      have hkS : k ∈ S := hFb_memS k hk
      have hfk : f k = b := hFb_f k hk
      have hd := hf_dist k hkS
      rw [hfk] at hd
      simpa [dist_comm] using hd
    have hFb_pair_c : ∀ i ∈ Fb, ∀ j ∈ Fb, i ≠ j →
        dist (T i).center (T j).center ≤ (ρ : ℝ) / 8 := by
      intro i hi j hj hij
      calc
        dist (T i).center (T j).center ≤
            dist (T i).center (T b).center + dist (T b).center (T j).center :=
          dist_triangle _ _ _
        _ ≤ (ρ : ℝ) / 16 + (ρ : ℝ) / 16 := by
          exact add_le_add (by simpa [dist_comm] using hFb_center i hi) (hFb_center j hj)
        _ = (ρ : ℝ) / 8 := by ring
    have hFb_dproj : ∀ i ∈ Fb, ∀ j ∈ Fb, i ≠ j →
        (ρ : ℝ) / 8 <
          min ‖(T i).direction - (T j).direction‖ ‖(T i).direction + (T j).direction‖ := by
      intro i hi j hj hij
      have hsep_lt := hSsep i (hFb_memS i hi) j (hFb_memS j hj) hij
      have hmk : (ρ : ℝ) / 8 < max (dist (T i).center (T j).center)
          (min ‖(T i).direction - (T j).direction‖ ‖(T i).direction + (T j).direction‖) := by
        simpa [tubeParamDist] using hsep_lt
      by_contra h
      have hmin_le : min ‖(T i).direction - (T j).direction‖ ‖(T i).direction + (T j).direction‖ ≤
          (ρ : ℝ) / 8 := le_of_not_gt h
      have hmax_le : max (dist (T i).center (T j).center)
          (min ‖(T i).direction - (T j).direction‖ ‖(T i).direction + (T j).direction‖) ≤
          (ρ : ℝ) / 8 := max_le (hFb_pair_c i hi j hj hij) hmin_le
      linarith
    have hFb_dirsep : ∀ i ∈ Fb, ∀ j ∈ Fb, i ≠ j →
        (ρ : ℝ) / 8 < ‖(T i).direction - (T j).direction‖ := by
      intro i hi j hj hij
      exact lt_of_lt_of_le (hFb_dproj i hi j hj hij) (min_le_left _ _)
    have hFbdir : (Fb.card : ℝ≥0∞) ≤ (ml1Boot.dirNet.C : ℝ≥0∞) * ((ρ / 8 : ℝ≥0) : ℝ≥0∞)⁻¹ ^ 2 :=
      card_le_of_direction_separated hdim T Fb (η := ρ / 8) hη₂0 hη₂1 hFb_dirsep
    simpa [Fb] using hFbdir
  -- STEP 5: multiply over the fibres.
  have hcast : (S.card : ℝ≥0∞) = ∑ b ∈ S', ((S.filter fun a => f a = b).card : ℝ≥0∞) := by
    rw [Finset.card_eq_sum_card_fiberwise hf_mem]
    exact Nat.cast_sum (s := S') (f := fun b => (S.filter fun a => f a = b).card)
  have hsum : ∑ b ∈ S', ((S.filter fun a => f a = b).card : ℝ≥0∞) ≤
      ∑ _b ∈ S', ((ml1Boot.dirNet.C : ℝ≥0∞) * ((ρ / 8 : ℝ≥0) : ℝ≥0∞)⁻¹ ^ 2) :=
    Finset.sum_le_sum hFib
  have hsum' : ∑ _b ∈ S', ((ml1Boot.dirNet.C : ℝ≥0∞) * ((ρ / 8 : ℝ≥0) : ℝ≥0∞)⁻¹ ^ 2) =
      (S'.card : ℝ≥0∞) * ((ml1Boot.dirNet.C : ℝ≥0∞) * ((ρ / 8 : ℝ≥0) : ℝ≥0∞)⁻¹ ^ 2) := by
    simp [Finset.sum_const]
  -- STEP 6: arithmetic.
  let a : ℝ≥0∞ := (ρ : ℝ≥0∞)
  have ha0 : a ≠ 0 := by
    dsimp [a]
    exact ENNReal.coe_ne_zero.mpr (ne_of_gt hρ0)
  have hatop : a ≠ ⊤ := ENNReal.coe_ne_top
  have hη₁e : ((ρ / 16 : ℝ≥0) : ℝ≥0∞) = a / 16 := by
    dsimp [a]
    rw [ENNReal.coe_div (by norm_num : (16 : ℝ≥0) ≠ 0)]
    norm_num
  have hη₂e : ((ρ / 8 : ℝ≥0) : ℝ≥0∞) = a / 8 := by
    dsimp [a]
    rw [ENNReal.coe_div (by norm_num : (8 : ℝ≥0) ≠ 0)]
    norm_num
  have hη₁inv : ((ρ / 16 : ℝ≥0) : ℝ≥0∞)⁻¹ = (16 : ℝ≥0∞) * a⁻¹ := by
    rw [hη₁e]
    rw [div_eq_mul_inv]
    rw [ENNReal.mul_inv (Or.inl ha0) (Or.inl hatop)]
    rw [inv_inv]
    rw [mul_comm]
  have hη₂inv : ((ρ / 8 : ℝ≥0) : ℝ≥0∞)⁻¹ = (8 : ℝ≥0∞) * a⁻¹ := by
    rw [hη₂e]
    rw [div_eq_mul_inv]
    rw [ENNReal.mul_inv (Or.inl ha0) (Or.inl hatop)]
    rw [inv_inv]
    rw [mul_comm]
  have hpow : ((ρ / 16 : ℝ≥0) : ℝ≥0∞)⁻¹ ^ 3 * ((ρ / 8 : ℝ≥0) : ℝ≥0∞)⁻¹ ^ 2 =
      (16 : ℝ≥0∞) ^ 3 * (8 : ℝ≥0∞) ^ 2 * (a⁻¹) ^ 5 := by
    rw [hη₁inv, hη₂inv]
    ring
  have hnum : (16 : ℝ≥0∞) ^ 3 * (8 : ℝ≥0∞) ^ 2 = 262144 := by norm_num
  have hrpow : (ρ : ℝ≥0∞) ^ (-5 : ℝ) = (a⁻¹) ^ (5 : ℕ) := by
    dsimp [a]
    rw [ENNReal.rpow_neg]
    simp only [ENNReal.rpow_ofNat]
    rw [ENNReal.inv_pow]
  calc
    (S.card : ℝ≥0∞) = ∑ b ∈ S', ((S.filter fun a => f a = b).card : ℝ≥0∞) := hcast
    _ ≤ ∑ _b ∈ S', ((ml1Boot.dirNet.C : ℝ≥0∞) * ((ρ / 8 : ℝ≥0) : ℝ≥0∞)⁻¹ ^ 2) := hsum
    _ = (S'.card : ℝ≥0∞) * ((ml1Boot.dirNet.C : ℝ≥0∞) * ((ρ / 8 : ℝ≥0) : ℝ≥0∞)⁻¹ ^ 2) := hsum'
    _ ≤ (ml1Boot.posNet.C : ℝ≥0∞) * ((ρ / 16 : ℝ≥0) : ℝ≥0∞)⁻¹ ^ 3 *
        ((ml1Boot.dirNet.C : ℝ≥0∞) * ((ρ / 8 : ℝ≥0) : ℝ≥0∞)⁻¹ ^ 2) := by
      exact mul_le_mul_of_nonneg_right hS'center bot_le
    _ = (hybridPackingConst : ℝ≥0∞) * (ρ : ℝ≥0∞) ^ (-5 : ℝ) := by
      dsimp [hybridPackingConst]
      rw [hrpow]
      calc
        (ml1Boot.posNet.C : ℝ≥0∞) * ((ρ / 16 : ℝ≥0) : ℝ≥0∞)⁻¹ ^ 3 *
            ((ml1Boot.dirNet.C : ℝ≥0∞) * ((ρ / 8 : ℝ≥0) : ℝ≥0∞)⁻¹ ^ 2)
            = (ml1Boot.posNet.C : ℝ≥0∞) * (ml1Boot.dirNet.C : ℝ≥0∞) *
                (((ρ / 16 : ℝ≥0) : ℝ≥0∞)⁻¹ ^ 3 * ((ρ / 8 : ℝ≥0) : ℝ≥0∞)⁻¹ ^ 2) := by ring
        _ = (ml1Boot.posNet.C : ℝ≥0∞) * (ml1Boot.dirNet.C : ℝ≥0∞) *
            ((16 : ℝ≥0∞) ^ 3 * (8 : ℝ≥0∞) ^ 2 * (a⁻¹) ^ 5) := by rw [hpow]
        _ = (ml1Boot.posNet.C : ℝ≥0∞) * (ml1Boot.dirNet.C : ℝ≥0∞) *
            (262144 * (a⁻¹) ^ 5) := by rw [hnum]
        _ = 262144 * (ml1Boot.posNet.C : ℝ≥0∞) * (ml1Boot.dirNet.C : ℝ≥0∞) * (a⁻¹) ^ 5 := by ring
        _ = ((262144 * ml1Boot.posNet.C * ml1Boot.dirNet.C : ℝ≥0) : ℝ≥0∞) * (a⁻¹) ^ 5 := by
          simp [ENNReal.coe_mul]
        _ = (hybridPackingConst : ℝ≥0∞) * (a⁻¹) ^ (5 : ℕ) := by rfl

end Packing

end Kakeya

end

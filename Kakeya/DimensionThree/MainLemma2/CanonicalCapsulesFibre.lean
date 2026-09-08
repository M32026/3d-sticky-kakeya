/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.CanonicalCapsules
public import Kakeya.Pigeonhole

/-!
# C7-b, the fibres: size bound, exact identities, and the bin-and-truncation shading

Source of record: the professor's refined proof
`260115_kakeyadetailedproofv3_revised_detailed.tex` , `propvnslocalization`
l.5373–5470: the fibre-size bound eqvnsfibresize (`#𝕋(S) ≤ 320 A r₁⁻²`), the exact identities
eqvnsfibreidentity / eqvnspointidentity, and the fibre regularisation eq:ml2-fibre-regularization
(l.3735–3743, l.5457–5470: "dyadically bin the positive values of `w_{c,S}` and select one joint
bin using the weights `∫_{Y'_c(S)} w_{c,S}`").  Status and the contract pins  and §8.  Additive; imports the geometry leaf.

## E — the fibre-size bound (refined eqvnsfibresize)

Every parent tube of a fibre lies in one convex body, the `2(1+L)`-dilate of the centred tube
of radius `fibreRadius/(2(1+L))` — `Kakeya.VeryNotSticky.fibreBody`, whose carrier is the closed
`fibreRadius`-neighbourhood of the segment of half-length `1 + L` on the net line
(`fibreRadius δ ε L = δ + ε(2 + 1/L)`: the tube's own radius plus the assignment slack over the
unit length).  `Kakeya.sum_volume_le_maxDensity_mul_volume'` then bounds the number of fibre
members by `Δ_max · |body| / (c₃ δ²)` (`CapsuleNet.card_fibre_mul_le`).

## F — the exact identities

* `CapsuleNet.card_filter_eq_sum_fibre` — the point identity eqvnspointidentity: a count over `I`
  is the sum over the net of the counts over the fibres (`Finset.card_eq_sum_card_fiberwise`).
* `sum_volume_inter_eq_lintegral_card` — the fibre identity eqvnsfibreidentity, for any finite
  family of measurable sets: `∑ᵢ |Sᵢ ∩ P| = ∫_P #{i : x ∈ Sᵢ}`.

## G — the bin-and-truncation shading (refined l.3735–3743, l.5457–5470)

For one fibre `F` with sets `S i` in a piece `P` and the weight `w(x) = #{i ∈ F : x ∈ S i}`, the
level-`m` bin is `{x ∈ P : m ≤ w x < 2m}` and the **truncated** sets keep, at each point of the
bin, exactly the `m` smallest (in a fixed linear order) of the `S i` containing it
(`Kakeya.VeryNotSticky.truncated`). Then the count is **exactly `m`** on the bin
(`card_filter_truncated`), so the `fibre` field of `BallDataCore` holds with `Cm = 1`; the
truncated sets are measurable; and their total mass is at least half the bin's weighted mass
(`sum_volume_inter_bin_le_two_mul`).
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

namespace Kakeya.VeryNotSticky

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {δ : NNReal}

/-! ### E — the containing body of a fibre, and the fibre-size bound -/

/-- `δ + ε·(2 + 1/L)`: the radius of the body containing every parent of a fibre. -/
noncomputable def fibreRadius (δ : NNReal) (ε L : ℝ) : ℝ := (δ : ℝ) + ε * (2 + 1 / L)

theorem fibreRadius_nonneg {ε L : ℝ} (hε : 0 ≤ ε) (hL : 0 < L) : 0 ≤ fibreRadius δ ε L := by
  unfold fibreRadius; positivity

/-- The radius of the centred tube whose `2(1+L)`-dilate is the containing body. -/
noncomputable def fibreBodyRadius (δ : NNReal) (ε L : ℝ) : NNReal :=
  Real.toNNReal (fibreRadius δ ε L / (2 * (1 + L)))

theorem coe_fibreBodyRadius {ε L : ℝ} (hε : 0 ≤ ε) (hL : 0 < L) :
    (fibreBodyRadius δ ε L : ℝ) = fibreRadius δ ε L / (2 * (1 + L)) :=
  Real.coe_toNNReal _ (div_nonneg (fibreRadius_nonneg hε hL) (by positivity))

/-- **The containing body of a fibre**: the `2(1+L)`-dilate of the centred tube of radius
`fibreRadius/(2(1+L))` — the closed `fibreRadius`-neighbourhood of the segment of half-length
`1 + L` on the net line. -/
noncomputable def fibreBody (T : Tube δ E3) (c : E3) (ε L : ℝ) : ConvexSpaceBody E3 :=
  Kakeya.Tube.dilate (centredTube T c (fibreBodyRadius δ ε L)) (2 * (1 + L))

theorem center_centredTube (T : Tube δ E3) (c : E3) (ρ : NNReal) :
    (centredTube T c ρ).center = foot T c := by
  change midpoint ℝ (centredTube T c ρ).x (centredTube T c ρ).y = foot T c
  rw [centredTube_x, centredTube_y, midpoint_eq_smul_add, invOf_eq_inv]
  module

theorem fibreBody_carrier (T : Tube δ E3) (c : E3) {ε L : ℝ} (hε : 0 ≤ ε) (hL : 0 < L) :
    (fibreBody T c ε L).carrier = cthickening (fibreRadius δ ε L)
      (segment ℝ (foot T c - (1 + L) • T.direction) (foot T c + (1 + L) • T.direction)) := by
  have hC : (0 : ℝ) < 2 * (1 + L) := by positivity
  rw [fibreBody, Kakeya.Tube.dilate_carrier_eq_cthickening _ hC, center_centredTube, centredTube_x,
    centredTube_y, homothety_sub_smul, homothety_add_smul, AffineMap.homothety_apply_same,
    coe_fibreBodyRadius hε hL]
  have h1 : 2 * (1 + L) * (fibreRadius δ ε L / (2 * (1 + L))) = fibreRadius δ ε L := by
    field_simp
  have h2 : 2 * (1 + L) * (1 / 2 : ℝ) = 1 + L := by ring
  rw [h1, h2]

/-- A point of a unit tube meeting `ball c r` (`r + δ ≤ L`) is within `δ` of a core point
`foot + s • d` with `|s| ≤ 1 + L`. -/
theorem exists_core_param_of_meets (T : Tube δ E3) (c : E3) {L r : ℝ} (hr : r + (δ : ℝ) ≤ L)
    (hmeet : (T.carrier ∩ ball c r).Nonempty) {x : E3} (hx : x ∈ T.carrier) :
    ∃ s : ℝ, |s| ≤ 1 + L ∧ dist x (foot T c + s • T.direction) ≤ δ := by
  obtain ⟨x₀, hx₀T, hx₀c⟩ := hmeet
  rw [T.carrier_eq] at hx₀T hx
  obtain ⟨z₀, hz₀, hx₀z₀⟩ := Set.mem_iUnion₂.mp hx₀T
  obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.mp hx
  rw [Metric.mem_closedBall] at hx₀z₀ hxz
  obtain ⟨t₀, ht₀, rfl⟩ := exists_corePt_of_mem_core T hz₀
  obtain ⟨t, ht, rfl⟩ := exists_corePt_of_mem_core T hz
  have hz₀c : dist (corePt T t₀) c ≤ L := by
    calc dist (corePt T t₀) c ≤ dist (corePt T t₀) x₀ + dist x₀ c := dist_triangle _ _ _
      _ ≤ δ + r := add_le_add (by rw [dist_comm]; exact hx₀z₀) (le_of_lt hx₀c)
      _ ≤ L := by linarith
  have hs₀ : |t₀ - footParam T c| ≤ L := by
    have h := abs_le_norm_foot_add_smul_sub T c (t₀ - footParam T c)
    rw [← corePt_eq_foot_add, ← dist_eq_norm] at h
    exact h.trans hz₀c
  have htt₀ : |t - t₀| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [ht.1, ht.2, ht₀.1, ht₀.2]
  refine ⟨t - footParam T c, ?_, ?_⟩
  · have : |t - footParam T c| ≤ |t - t₀| + |t₀ - footParam T c| := by
      calc |t - footParam T c| = |(t - t₀) + (t₀ - footParam T c)| := by ring_nf
        _ ≤ |t - t₀| + |t₀ - footParam T c| := abs_add_le _ _
    linarith
  · rw [← corePt_eq_foot_add]; exact hxz

/-- **Every parent of a fibre lies in the containing body**: a tube `ε`-close to `T'` (in the
parameter metric) and meeting `ball c r`, `r + δ ≤ L`, has its carrier inside
`fibreBody T' c ε L`. -/
theorem tube_subset_fibreBody_of_close (T T' : Tube δ E3) (c : E3) {ε L r : ℝ} (hε : 0 ≤ ε)
    (hL : 0 < L) (hr : r + (δ : ℝ) ≤ L)
    (hclose : ‖foot T c - foot T' c‖ + L * ‖T.direction - T'.direction‖ ≤ ε)
    (hmeet : (T.carrier ∩ ball c r).Nonempty) :
    T.carrier ⊆ (fibreBody T' c ε L).carrier := by
  rw [fibreBody_carrier T' c hε hL]
  intro x hx
  obtain ⟨s, hs, hxs⟩ := exists_core_param_of_meets T c hr hmeet hx
  have hdir : ‖T.direction - T'.direction‖ ≤ ε / L := by
    rw [le_div_iff₀ hL]
    linarith [norm_nonneg (foot T c - foot T' c)]
  have hfoot : ‖foot T c - foot T' c‖ ≤ ε := by
    linarith [mul_nonneg hL.le (norm_nonneg (T.direction - T'.direction))]
  -- the corresponding point on the net line
  have hw : foot T' c + s • T'.direction ∈
      segment ℝ (foot T' c - (1 + L) • T'.direction) (foot T' c + (1 + L) • T'.direction) := by
    rw [segment_eq_image']
    have hs' := abs_le.mp hs
    have h2L : (0 : ℝ) < 2 * (1 + L) := by positivity
    refine ⟨(s + (1 + L)) / (2 * (1 + L)), ⟨div_nonneg (by linarith) h2L.le, ?_⟩, ?_⟩
    · rw [div_le_one h2L]; linarith
    · have hθ : (s + (1 + L)) / (2 * (1 + L)) * (2 * (1 + L)) = s + (1 + L) := by
        field_simp
      have h3 : foot T' c + (1 + L) • T'.direction - (foot T' c - (1 + L) • T'.direction)
          = (2 * (1 + L)) • T'.direction := by module
      change foot T' c - (1 + L) • T'.direction + ((s + (1 + L)) / (2 * (1 + L))) •
        (foot T' c + (1 + L) • T'.direction - (foot T' c - (1 + L) • T'.direction))
          = foot T' c + s • T'.direction
      rw [h3, smul_smul, hθ]
      module
  refine mem_cthickening_of_dist_le x _ _ _ hw ?_
  calc dist x (foot T' c + s • T'.direction)
      ≤ dist x (foot T c + s • T.direction) +
        dist (foot T c + s • T.direction) (foot T' c + s • T'.direction) := dist_triangle _ _ _
    _ ≤ δ + (ε + (1 + L) * (ε / L)) := by
        refine add_le_add hxs ?_
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

/-- **The fibre-size bound** (refined eqvnsfibresize, `#𝕋(S) ≤ 320 A r₁⁻²`): for a capsule net
on a family `I ⊆ s` of tubes meeting `ball c r` (`r + δ ≤ L`), every fibre has
`#fibre · c₃ δ² ≤ Δ_max(s) · |fibreBody|`, with `|fibreBody| ≤ (2(1+L))³ · 16 · ρ''²`,
`ρ'' = fibreRadius/(2(1+L))`. -/
theorem CapsuleNet.card_fibre_mul_le {ι : Type*} {I : Finset ι} {T : ι → Tube δ E3} {c : E3}
    {L ε : ℝ} (𝒩 : CapsuleNet I T c L ε) {s : Finset ι} (hI : I ⊆ s) (hε : 0 ≤ ε) (hL : 0 < L)
    {r : ℝ} (hr : r + (δ : ℝ) ≤ L) (hmeet : ∀ i ∈ I, ((T i).carrier ∩ ball c r).Nonempty)
    (hrad : fibreRadius δ ε L ≤ 2 * (1 + L)) [DecidableEq ι] (ν : ι) :
    ((𝒩.fibre ν).card : ENNReal) * ((Tube.le_volume.c 3 : ENNReal) * (δ : ENNReal) ^ 2) ≤
      maxDensity s (fun i ↦ (T i).toConvexSpaceBody) *
        (ENNReal.ofReal ((2 * (1 + L)) ^ 3) *
          ((Tube.volume_le.C 3 : ENNReal) * (fibreBodyRadius δ ε L : ENNReal) ^ 2)) := by
  classical
  set W : ι → ConvexSpaceBody E3 := fun i ↦ (T i).toConvexSpaceBody with hW
  have hcont : ∀ i ∈ 𝒩.fibre ν, W i ≤ fibreBody (T ν) c ε L := by
    intro i hi
    change (T i).carrier ⊆ (fibreBody (T ν) c ε L).carrier
    exact tube_subset_fibreBody_of_close (T i) (T ν) c hε hL hr
      (le_of_lt (𝒩.close_of_mem_fibre hi)) (hmeet i (𝒩.fibre_subset ν hi))
  have hsum := sum_volume_le_maxDensity_mul_volume' hcont
  have hmono : maxDensity (𝒩.fibre ν) W ≤ maxDensity s W :=
    maxDensity_mono W ((𝒩.fibre_subset ν).trans hI)
  have hlow : ∀ i ∈ 𝒩.fibre ν,
      (Tube.le_volume.c 3 : ENNReal) * (δ : ENNReal) ^ 2 ≤ volume (W i).carrier := by
    intro i _
    have h := Tube.le_volume (T i)
    rw [finrank_euclideanSpace_fin] at h
    simpa using h
  have hcard : ((𝒩.fibre ν).card : ENNReal) *
      ((Tube.le_volume.c 3 : ENNReal) * (δ : ENNReal) ^ 2) ≤
        ∑ i ∈ 𝒩.fibre ν, volume (W i).carrier := by
    have := Finset.card_nsmul_le_sum (𝒩.fibre ν) (fun i => volume (W i).carrier) _ hlow
    simpa [nsmul_eq_mul] using this
  have hvol : volume (fibreBody (T ν) c ε L).carrier ≤
      ENNReal.ofReal ((2 * (1 + L)) ^ 3) *
        ((Tube.volume_le.C 3 : ENNReal) * (fibreBodyRadius δ ε L : ENNReal) ^ 2) := by
    have hC : (1 : ℝ) < 2 * (1 + L) := by linarith
    rw [fibreBody, Kakeya.Tube.tubeDilateVolume _ hC, finrank_euclideanSpace_fin]
    have hρ1 : fibreBodyRadius δ ε L ≤ 1 := by
      rw [← NNReal.coe_le_coe, coe_fibreBodyRadius hε hL, NNReal.coe_one,
        div_le_one (by positivity)]
      exact hrad
    have h := Tube.volume_le hρ1 (centredTube (T ν) c (fibreBodyRadius δ ε L))
    rw [finrank_euclideanSpace_fin] at h
    gcongr
  calc ((𝒩.fibre ν).card : ENNReal) * ((Tube.le_volume.c 3 : ENNReal) * (δ : ENNReal) ^ 2)
      ≤ ∑ i ∈ 𝒩.fibre ν, volume (W i).carrier := hcard
    _ ≤ maxDensity (𝒩.fibre ν) W * volume (fibreBody (T ν) c ε L).carrier := hsum
    _ ≤ maxDensity s W * (ENNReal.ofReal ((2 * (1 + L)) ^ 3) *
          ((Tube.volume_le.C 3 : ENNReal) * (fibreBodyRadius δ ε L : ENNReal) ^ 2)) :=
        mul_le_mul' hmono hvol

/-! ### F — the exact identities -/

/-- **The point identity** (refined eqvnspointidentity): a count over `I` is the sum over the
net of the counts over the fibres. -/
theorem CapsuleNet.card_filter_eq_sum_fibre {ι : Type*} {I : Finset ι} {T : ι → Tube δ E3}
    {c : E3} {L ε : ℝ} (𝒩 : CapsuleNet I T c L ε) [DecidableEq ι] (p : ι → Prop)
    [DecidablePred p] :
    (I.filter p).card = ∑ ν ∈ 𝒩.net, ((𝒩.fibre ν).filter p).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := 𝒩.assign) (t := 𝒩.net)
    (fun i hi => 𝒩.assign_mem i (Finset.mem_filter.1 (Finset.mem_coe.1 hi)).1)]
  refine Finset.sum_congr rfl fun ν _ => ?_
  congr 1
  ext i
  simp only [Finset.mem_filter, CapsuleNet.fibre]
  tauto

open scoped Classical in
/-- **The fibre identity** (refined eqvnsfibreidentity), for any finite family of measurable
sets: `∑ᵢ |Sᵢ ∩ P| = ∫_P #{i : x ∈ Sᵢ}`. -/
theorem sum_volume_inter_eq_lintegral_card {ι : Type*} (F : Finset ι) (S : ι → Set E3)
    (hS : ∀ i ∈ F, MeasurableSet (S i)) (P : Set E3) :
    ∑ i ∈ F, volume (S i ∩ P) =
      ∫⁻ x in P, (((F.filter fun i => x ∈ S i).card : ℕ) : ENNReal) := by
  classical
  have h1 : ∀ i ∈ F, volume (S i ∩ P) = ∫⁻ x in P, (S i).indicator (1 : E3 → ENNReal) x := by
    intro i hi
    rw [lintegral_indicator_one (hS i hi), Measure.restrict_apply (hS i hi)]
  rw [Finset.sum_congr rfl h1,
    ← lintegral_finsetSum F (fun i hi => (measurable_one.indicator (hS i hi)))]
  refine lintegral_congr fun x => ?_
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hx : x ∈ S i <;> simp [hx]

/-! ### G — the bin-and-truncation shading, per fibre -/

section Truncation

variable {ι : Type*} [LinearOrder ι]

/-- The `m` smallest members of `G` in the linear order (the truncation rule: the point keeps
the `m` smallest indices of the sets containing it). -/
def firstM (m : ℕ) (G : Finset ι) : Finset ι := ((G.sort (· ≤ ·)).take m).toFinset

theorem firstM_subset (m : ℕ) (G : Finset ι) : firstM m G ⊆ G := by
  intro i hi
  rw [firstM, List.mem_toFinset] at hi
  exact (Finset.mem_sort (· ≤ ·)).1 (List.mem_of_mem_take hi)

theorem card_firstM (m : ℕ) (G : Finset ι) : (firstM m G).card = min m G.card := by
  rw [firstM, List.toFinset_card_of_nodup
    ((Finset.sort_nodup G (· ≤ ·)).sublist (List.take_sublist m _)), List.length_take,
    Finset.length_sort]

omit [LinearOrder ι] in
open scoped Classical in
/-- The weight `w(x) = #{i ∈ F : x ∈ S i}` (refined `w_{c,S}`, l.3714). -/
noncomputable def fibreWeight (F : Finset ι) (S : ι → Set E3) (x : E3) : ℕ :=
  (F.filter fun i => x ∈ S i).card

omit [LinearOrder ι] in
/-- The level-`m` bin: the points of `P` with `m ≤ w x < 2m`. -/
def levelBin (F : Finset ι) (S : ι → Set E3) (P : Set E3) (m : ℕ) : Set E3 :=
  {x ∈ P | m ≤ fibreWeight F S x ∧ fibreWeight F S x < 2 * m}

open scoped Classical in
/-- **The truncated set of `i`**: the points of `S i` in the bin at which `i` is among the `m`
smallest members of `F` whose set contains the point. -/
def truncated (F : Finset ι) (S : ι → Set E3) (P : Set E3) (m : ℕ) (i : ι) : Set E3 :=
  {x ∈ S i ∩ levelBin F S P m | i ∈ firstM m (F.filter fun j => x ∈ S j)}

theorem truncated_subset (F : Finset ι) (S : ι → Set E3) (P : Set E3) (m : ℕ) (i : ι) :
    truncated F S P m i ⊆ S i ∩ P :=
  fun _ hx => ⟨hx.1.1, hx.1.2.1⟩

theorem truncated_subset_levelBin (F : Finset ι) (S : ι → Set E3) (P : Set E3) (m : ℕ)
    (i : ι) : truncated F S P m i ⊆ levelBin F S P m :=
  fun _ hx => hx.1.2

open scoped Classical in
theorem filter_truncated_eq (F : Finset ι) (S : ι → Set E3) (P : Set E3) (m : ℕ) {x : E3}
    (hx : x ∈ levelBin F S P m) :
    (F.filter fun i => x ∈ truncated F S P m i) = firstM m (F.filter fun j => x ∈ S j) := by
  ext i
  simp only [Finset.mem_filter, truncated, Set.mem_setOf_eq, Set.mem_inter_iff]
  constructor
  · rintro ⟨-, -, h⟩
    exact h
  · intro h
    have hi : i ∈ F.filter fun j => x ∈ S j := firstM_subset _ _ h
    rw [Finset.mem_filter] at hi
    exact ⟨hi.1, ⟨hi.2, hx⟩, h⟩

open scoped Classical in
/-- **Exactly `m` truncated sets contain each point of the bin** — the `fibre` field of
`BallDataCore` at `Cm = 1`. -/
theorem card_filter_truncated (F : Finset ι) (S : ι → Set E3) (P : Set E3) (m : ℕ) {x : E3}
    (hx : x ∈ levelBin F S P m) :
    (F.filter fun i => x ∈ truncated F S P m i).card = m := by
  rw [filter_truncated_eq F S P m hx, card_firstM]
  exact min_eq_left hx.2.1

open scoped Classical in
theorem card_filter_truncated_eq_zero (F : Finset ι) (S : ι → Set E3) (P : Set E3) (m : ℕ)
    {x : E3} (hx : x ∉ levelBin F S P m) :
    (F.filter fun i => x ∈ truncated F S P m i).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i _ hi
  exact hx hi.1.2

omit [LinearOrder ι] in
theorem measurable_fibreWeight (F : Finset ι) (S : ι → Set E3)
    (hS : ∀ i ∈ F, MeasurableSet (S i)) : Measurable (fun x => fibreWeight F S x) := by
  classical
  have h : (fun x => fibreWeight F S x) =
      fun x => ∑ i ∈ F, (S i).indicator (fun _ => (1 : ℕ)) x := by
    ext x
    rw [fibreWeight, Finset.card_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hx : x ∈ S i <;> simp [hx]
  rw [h]
  exact Finset.measurable_sum F fun i hi => measurable_const.indicator (hS i hi)

omit [LinearOrder ι] in
theorem measurableSet_levelBin (F : Finset ι) (S : ι → Set E3) {P : Set E3}
    (hS : ∀ i ∈ F, MeasurableSet (S i)) (hP : MeasurableSet P) (m : ℕ) :
    MeasurableSet (levelBin F S P m) := by
  have h : levelBin F S P m = P ∩ (fun x => fibreWeight F S x) ⁻¹' (Set.Ico m (2 * m)) := by
    ext x
    simp only [levelBin, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ico]
  rw [h]
  exact hP.inter (measurable_fibreWeight F S hS MeasurableSet.of_discrete)

open scoped Classical in
theorem measurableSet_truncated (F : Finset ι) (S : ι → Set E3) {P : Set E3}
    (hS : ∀ i ∈ F, MeasurableSet (S i)) (hP : MeasurableSet P) (m : ℕ) {i : ι} (hi : i ∈ F) :
    MeasurableSet (truncated F S P m i) := by
  have hfib : ∀ G : Finset ι, G ⊆ F →
      MeasurableSet {x : E3 | (F.filter fun j => x ∈ S j) = G} := by
    intro G hG
    have h : {x : E3 | (F.filter fun j => x ∈ S j) = G} =
        (⋂ j ∈ G, S j) ∩ (⋂ j ∈ F \ G, (S j)ᶜ) := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_compl_iff,
        Finset.mem_sdiff]
      constructor
      · intro h
        refine ⟨fun j hj => ?_, fun j hj hx => ?_⟩
        · rw [← h, Finset.mem_filter] at hj
          exact hj.2
        · have : j ∈ G := by
            rw [← h, Finset.mem_filter]
            exact ⟨hj.1, hx⟩
          exact hj.2 this
      · rintro ⟨h1, h2⟩
        ext j
        rw [Finset.mem_filter]
        constructor
        · rintro ⟨hjF, hx⟩
          by_contra hjG
          exact h2 j ⟨hjF, hjG⟩ hx
        · intro hjG
          exact ⟨hG hjG, h1 j hjG⟩
    rw [h]
    exact (Finset.measurableSet_biInter G fun j hj => hS j (hG hj)).inter
      (Finset.measurableSet_biInter (F \ G) fun j hj => (hS j (Finset.mem_sdiff.1 hj).1).compl)
  have hset : {x : E3 | i ∈ firstM m (F.filter fun j => x ∈ S j)} =
      ⋃ G ∈ (F.powerset.filter fun G => i ∈ firstM m G),
        {x : E3 | (F.filter fun j => x ∈ S j) = G} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_filter, Finset.mem_powerset,
      exists_prop]
    constructor
    · intro h
      exact ⟨F.filter fun j => x ∈ S j, ⟨Finset.filter_subset _ _, h⟩, rfl⟩
    · rintro ⟨G, ⟨-, hG⟩, rfl⟩
      exact hG
  have h : truncated F S P m i = (S i ∩ levelBin F S P m) ∩
      {x : E3 | i ∈ firstM m (F.filter fun j => x ∈ S j)} := by
    ext x
    simp only [truncated, Set.mem_setOf_eq, Set.mem_inter_iff]
  rw [h, hset]
  exact ((hS i hi).inter (measurableSet_levelBin F S hS hP m)).inter
    (Finset.measurableSet_biUnion _ fun G hG =>
      hfib G (Finset.mem_powerset.1 (Finset.mem_filter.1 hG).1))

open scoped Classical in
/-- **The truncated mass is exactly `m` times the bin's volume** (the fibre identity on the
truncated sets, whose count is `m` on the bin and `0` off it). -/
theorem sum_volume_truncated (F : Finset ι) (S : ι → Set E3) {P : Set E3}
    (hS : ∀ i ∈ F, MeasurableSet (S i)) (hP : MeasurableSet P) (m : ℕ) :
    ∑ i ∈ F, volume (truncated F S P m i) = m * volume (levelBin F S P m) := by
  have hbin := measurableSet_levelBin F S hS hP m
  have h1 : ∀ i ∈ F, volume (truncated F S P m i) =
      volume (truncated F S P m i ∩ levelBin F S P m) := by
    intro i _
    congr 1
    exact (Set.inter_eq_left.2 (truncated_subset_levelBin F S P m i)).symm
  rw [Finset.sum_congr rfl h1,
    sum_volume_inter_eq_lintegral_card F _ (fun i hi => measurableSet_truncated F S hS hP m hi)
      _,
    setLIntegral_congr_fun hbin (fun x hx => by rw [card_filter_truncated F S P m hx]),
    setLIntegral_const]

open scoped Classical in
/-- **The bin's weighted mass is at most twice the truncated mass**: `∑ᵢ |Sᵢ ∩ bin| = ∫_bin w ≤
2m |bin| = 2 ∑ᵢ |truncatedᵢ|` — the factor `2` of the `Cg` ledger. -/
theorem sum_volume_inter_levelBin_le_two_mul (F : Finset ι) (S : ι → Set E3) {P : Set E3}
    (hS : ∀ i ∈ F, MeasurableSet (S i)) (hP : MeasurableSet P) (m : ℕ) :
    ∑ i ∈ F, volume (S i ∩ levelBin F S P m) ≤ 2 * ∑ i ∈ F, volume (truncated F S P m i) := by
  have hbin := measurableSet_levelBin F S hS hP m
  rw [sum_volume_inter_eq_lintegral_card F S hS _, sum_volume_truncated F S hS hP m]
  calc ∫⁻ x in levelBin F S P m, (((F.filter fun i => x ∈ S i).card : ℕ) : ENNReal)
      ≤ ∫⁻ _ in levelBin F S P m, ((2 * m : ℕ) : ENNReal) := by
        refine setLIntegral_mono measurable_const fun x hx => ?_
        exact_mod_cast hx.2.2.le
    _ = 2 * (m * volume (levelBin F S P m)) := by
        rw [setLIntegral_const]
        push_cast
        ring

/-! ### G2 — the dyadic partition of a piece into bins, and the level selection -/

omit [LinearOrder ι] in
open scoped Classical in
/-- **The bins at the dyadic levels partition the shaded part of the piece**: for `x ∈ S i ∩ P`
the weight is in `[1, #F]`, so `x` lies in the bin of level `2 ^ Nat.log 2 (w x)`, and in no
other. -/
theorem inter_eq_biUnion_levelBin (F : Finset ι) (S : ι → Set E3) (P : Set E3) {i : ι}
    (hi : i ∈ F) :
    S i ∩ P = ⋃ k ∈ Finset.range (Nat.log 2 F.card + 1), (S i ∩ levelBin F S P (2 ^ k)) := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_iUnion, Finset.mem_range, exists_prop]
  constructor
  · rintro ⟨hxS, hxP⟩
    have hw1 : 1 ≤ fibreWeight F S x :=
      Finset.card_pos.2 ⟨i, Finset.mem_filter.2 ⟨hi, hxS⟩⟩
    have hwF : fibreWeight F S x ≤ F.card := Finset.card_filter_le _ _
    refine ⟨Nat.log 2 (fibreWeight F S x), ?_, hxS, hxP, ?_, ?_⟩
    · exact Nat.lt_succ_of_le (Nat.log_mono_right hwF)
    · exact Nat.pow_log_le_self 2 (by omega)
    · rw [← pow_succ']
      exact Nat.lt_pow_succ_log_self (by norm_num) _
  · rintro ⟨k, -, hxS, hxP, -⟩
    exact ⟨hxS, hxP⟩

omit [LinearOrder ι] in
open scoped Classical in
theorem pairwiseDisjoint_levelBin (F : Finset ι) (S : ι → Set E3) (P : Set E3) :
    (↑(Finset.range (Nat.log 2 F.card + 1)) : Set ℕ).PairwiseDisjoint
      fun k => levelBin F S P (2 ^ k) := by
  intro k _ l _ hkl
  rw [Function.onFun, Set.disjoint_left]
  intro x hxk hxl
  apply hkl
  have h1 := hxk.2
  have h2 := hxl.2
  -- `2^k ≤ w < 2^(k+1)` and `2^l ≤ w < 2^(l+1)` force `k = l`
  have hk : Nat.log 2 (fibreWeight F S x) = k := by
    rw [← pow_succ'] at h1
    exact Nat.log_eq_of_pow_le_of_lt_pow h1.1 h1.2
  have hl : Nat.log 2 (fibreWeight F S x) = l := by
    rw [← pow_succ'] at h2
    exact Nat.log_eq_of_pow_le_of_lt_pow h2.1 h2.2
  rw [← hk, ← hl]

omit [LinearOrder ι] in
open scoped Classical in
/-- The mass of a set in the piece is the sum of its masses in the dyadic bins. -/
theorem volume_inter_eq_sum_levelBin (F : Finset ι) (S : ι → Set E3) {P : Set E3}
    (hS : ∀ i ∈ F, MeasurableSet (S i)) (hP : MeasurableSet P) {i : ι} (hi : i ∈ F) :
    volume (S i ∩ P) =
      ∑ k ∈ Finset.range (Nat.log 2 F.card + 1), volume (S i ∩ levelBin F S P (2 ^ k)) := by
  rw [inter_eq_biUnion_levelBin F S P hi]
  rw [measure_biUnion_finset]
  · intro k hk l hl hkl
    exact ((pairwiseDisjoint_levelBin F S P) hk hl hkl).mono Set.inter_subset_right
      Set.inter_subset_right
  · intro k _
    exact (hS i hi).inter (measurableSet_levelBin F S hS hP (2 ^ k))

end Truncation

/-- **The level selection** (refined l.5462–5470: "select one joint bin using the weights"):
for finitely many fibres `j ∈ J`, each with a total mass `total j` split over `K` levels as
`g j k` (`∑_{k<K} g j k = total j`), some level `k < K` carries at least `1/K` of the total:
`∑_j total j ≤ K · ∑_j g j k`.  `ENNReal.exists_card_inv_mul_sum_le` over the levels, after
swapping the two sums. -/
theorem exists_level_of_bins {κ : Type*} (J : Finset κ) (K : ℕ) (hK : 0 < K)
    (g : κ → ℕ → ENNReal) (total : κ → ENNReal)
    (hsplit : ∀ j ∈ J, ∑ k ∈ Finset.range K, g j k = total j) :
    ∃ k ∈ Finset.range K, ∑ j ∈ J, total j ≤ (K : ENNReal) * ∑ j ∈ J, g j k := by
  obtain ⟨k, hk, hle⟩ := ENNReal.exists_card_inv_mul_sum_le (T := Finset.range K)
    ⟨0, Finset.mem_range.2 hK⟩ (fun k => ∑ j ∈ J, g j k)
  refine ⟨k, hk, ?_⟩
  rw [Finset.card_range] at hle
  have hswap : ∑ k ∈ Finset.range K, ∑ j ∈ J, g j k = ∑ j ∈ J, total j := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl hsplit
  rw [hswap, ENNReal.inv_mul_le_iff (by exact_mod_cast hK.ne') (ENNReal.natCast_ne_top _)]
    at hle
  exact hle

end Kakeya.VeryNotSticky

end

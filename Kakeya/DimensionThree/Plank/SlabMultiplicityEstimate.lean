/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Slab.Incidence
public import Kakeya.DimensionThree.Plank.SlabFamilyControl
public import Kakeya.DimensionThree.Plank.RepresentativeFibres

/-!
# GWZ Lemma 6.9: the slab multiplicity and union-volume estimate

GWZ Lemma 6.8 (`ShadedSlab.fullness_sq_angle_le_volume_union`, proved in
`Kakeya/DimensionThree/SlabEstimate.lean`) bounds the incidence mass of a family of `δ × 1 × 1`
slabs by `|s| ^ 2 · δ ^ 2 / θ` at a typical intersection angle `θ`.  For a family which does not
*concentrate* — `Δ_max(𝒮) ≤ Δ` — that bound can be improved by a whole factor of the cardinality:
the slabs of the family which both make angle `≲ θ` with a fixed slab `S_i` and meet it are all
contained in one `O(θ)`-slab about `S_i`, and `Δ_max` bounds their number by `O(Δ · θ / δ)`.  Since
two slabs at angle `≈ θ` meet in volume `O(δ ^ 2 / θ)`, the two factors of `θ` cancel and

`Tri_θ(𝒮, Y) ≤ C · Δ · |s| · δ`

(`ShadedSlab.triAtAngle_le_maxDensity_mul`), *linear* in `|s|`.  Feeding this into the `L ^ 2`
method gives GWZ Lemma 6.9 in the two forms the paper states:

* `ShadedSlab.multiplicity_mul_le_of_typicalAngle` — the multiplicity bound
  `μ(𝒮, Y) · 8λ ≤ C · M · Δ`, i.e. `μ ≲ M · Δ / λ`;
* `ShadedSlab.sq_fullness_mul_le_volume_union` — the union-volume bound
  `64 λ ^ 2 |s| δ ≤ C · M · Δ · |U(𝒮, Y)|`.

Both are sharper than the paper's `δ ^ (-8η)` / `δ ^ (8η)`: with `λ ≥ δ ^ η`, `Δ ≤ δ ^ (-η)` and a
typical-angle loss `M ≤ δ ^ (-η)` the first gives `μ ≲ δ ^ (-3η)`
(`ShadedSlab.slabMultiplicityEstimate`).  Nothing here is specific to Section 6: the statements
mention neither planks nor factorisations, and the typical angle enters exactly as it does in
Lemma 6.8, as an explicit `(θ, M)` pair.

## The two Section-6 consumers

The large-`b` branches of GWZ Proposition 6.6(A) and 6.6(B) are the intended consumers.  What they
need on top of Lemma 6.9 is pure `ENNReal` algebra, isolated at the end of this file as
`Kakeya.partATarget_of_multiplicity_le` and `Kakeya.partBTarget_of_multiplicity_le`; the docstrings
there record precisely which scale hypothesis each consumer must supply (and which one is currently
missing from the two fallback wrappers).
-/

@[expose] public section

open MeasureTheory Convexity ConvexSpaceBody Kakeya
open scoped NNReal ENNReal Classical

noncomputable section

namespace ShadedSlab

variable {δ : ℝ≥0} {h : δ ≤ 1} {ι : Type*}

/-! ### The angular cluster of a slab -/

/-- **The `θ`-cluster of the slab `V i`**: those members of the family which contribute to
`ShadedSlab.triAtAngle` through the term `i`, i.e. whose angle with `V i` lies in the window
`[θ - δ, 2θ]` *and* whose carrier meets that of `V i`.  Members whose carrier misses `V i` contribute
nothing to the incidence mass, and it is only for the ones that meet `V i` that the angle window
forces containment in a common `O(θ)`-slab. -/
def angleCluster (s : Finset ι) (V : ι → ShadedSlab δ h) (i : ι) (θ : ℝ) : Finset ι :=
  {j ∈ s | (θ - δ ≤ Slab.angle (V i).toPrism3D (V j).toPrism3D ∧
      Slab.angle (V i).toPrism3D (V j).toPrism3D ≤ 2 * θ) ∧
      ((V i).carrier ∩ (V j).carrier : Set (EuclideanSpace ℝ (Fin 3))).Nonempty}

theorem angleCluster_subset (s : Finset ι) (V : ι → ShadedSlab δ h) (i : ι) (θ : ℝ) :
    angleCluster s V i θ ⊆ s := Finset.filter_subset _ _

/-- **A slab meeting `S` at angle `≲ θ` lies in a fixed dilate of the `θ`-slab about `S`.**

The `δ`-slab `S'` is in particular a `δ × 1 × 1` plank, and `Slab.reslab` widens `S` to the `θ`-slab
with the same centre and frame, so `Plank.plank_subset_dilation_of_angle_le` applies with `K = 2`
(the angle window) and `Cset = 1` (the meeting point lies in `S ⊆ S.reslab θ`), giving the dilation
factor `1 + 4 · 2 + 8 = 17`.

This is the geometric heart of the improvement of Lemma 6.8 used below: without it one can only say
that the cluster is the whole family. -/
theorem carrier_subset_dilation_reslab {θ : ℝ≥0} {hθ1 : θ ≤ 1} (S S' : Slab δ h)
    (hδθ : δ ≤ θ) (hang : Prism3D.angle S S' ≤ 2 * (θ : ℝ))
    (hne : ((S.carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩ S'.carrier).Nonempty) :
    (S'.carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
      ((S.reslab θ hθ1).toPrismNDim.dilation 17).carrier := by
  obtain ⟨p, hpS, hpS'⟩ := hne
  have haθb : δ ≤ θ * (1 : ℝ≥0) := by simpa using hδθ
  have hangle : Prism3D.angle S' (S.reslab θ hθ1) ≤ (2 : ℝ) * (θ : ℝ) := by
    rw [Slab.angle_reslab S' S θ hθ1, Prism3D.angle_comm S' S]
    exact hang
  have hcarrier : (S.carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
      ((S.reslab θ hθ1).carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
    intro x hx
    rw [show (S.reslab θ hθ1).carrier = (S.toPrismNDim.resize ![θ, (1 : ℝ≥0), 1]).carrier from rfl]
    rw [PrismNDim.mem_resize_carrier]
    intro i
    have h := ((PrismNDim.mem_carrier_iff S.toPrismNDim x).1 hx i)
    refine h.trans ?_
    rw [Prism3D.thicknesses_eq S]
    fin_cases i
    · simp [hδθ]
    · simp
    · simp
  have hpSres : p ∈ ((S.reslab θ hθ1).toPrismNDim.dilation 1).carrier :=
    (PrismNDim.self_subset_dilation (S.reslab θ hθ1).toPrismNDim le_rfl) (hcarrier hpS)
  have h := Plank.plank_subset_dilation_of_angle_le (V := S') (S := S.reslab θ hθ1)
    (K := 2) (Cset := 1) haθb hangle hpS' hpSres
  convert h using 2; norm_num

/-- **The cluster count.**  If the family has `Δ_max ≤ Δ` then the `θ`-cluster of any of its slabs
has at most `17 ^ 3 · Δ · θ / δ` members, in the division-free form below: all its members lie in the
`17`-dilate of the `θ`-slab about `V i`, whose volume is `17 ^ 3 · 8θ`, and each contributes volume
`8δ` to the density in that body. -/
theorem card_angleCluster_mul_le {θ : ℝ≥0} (hθ1 : θ ≤ 1) (s : Finset ι) (V : ι → ShadedSlab δ h)
    (hδθ : δ ≤ θ) {Δ : ENNReal}
    (hΔ : maxDensity s (fun j => (V j).toConvexSpaceBody) ≤ Δ) (i : ι) :
    ((angleCluster s V i (θ : ℝ)).card : ENNReal) * (8 * (δ : ENNReal))
      ≤ Δ * ((4913 : ENNReal) * (8 * (θ : ENNReal))) := by
  classical
  let W : ι → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) := fun j => (V j).toConvexSpaceBody
  let K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) :=
    ((Slab.reslab (V i).toPrism3D θ hθ1).toPrismNDim.dilation 17).toConvexSpaceBody
  -- every member of the cluster has its body inside K
  have hmem : ∀ j ∈ angleCluster s V i (θ : ℝ), W j ≤ K := by
    intro j hj
    have hj' : j ∈ s ∧ (θ - δ ≤ Slab.angle (V i).toPrism3D (V j).toPrism3D ∧
        Slab.angle (V i).toPrism3D (V j).toPrism3D ≤ 2 * (θ : ℝ)) ∧
        ((V i).carrier ∩ (V j).carrier : Set (EuclideanSpace ℝ (Fin 3))).Nonempty := by
      simpa [angleCluster] using hj
    have hang : Prism3D.angle (V i).toPrism3D (V j).toPrism3D ≤ 2 * (θ : ℝ) := hj'.2.1.2
    have hne : ((V i).carrier ∩ (V j).carrier : Set (EuclideanSpace ℝ (Fin 3))).Nonempty := hj'.2.2
    have hsub : ((V j).carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
        ((Slab.reslab (V i).toPrism3D θ hθ1).toPrismNDim.dilation 17).carrier :=
      carrier_subset_dilation_reslab (V i).toPrism3D (V j).toPrism3D hδθ hang hne
    exact SetLike.coe_subset_coe.mpr hsub
  -- cluster lies in the density filter
  have hcluster : angleCluster s V i (θ : ℝ) ⊆ s.filter (fun j => W j ≤ K) := by
    intro j hj
    rw [Finset.mem_filter]
    exact ⟨angleCluster_subset s V i (θ : ℝ) hj, hmem j hj⟩
  have hsum_le : (∑ j ∈ angleCluster s V i (θ : ℝ), volume (V j).carrier) ≤
      ∑ j ∈ s with W j ≤ K, volume (V j).carrier := by
    exact Finset.sum_le_sum_of_subset hcluster
  have hsum_cluster : (∑ j ∈ angleCluster s V i (θ : ℝ), volume (V j).carrier)
      = ((angleCluster s V i (θ : ℝ)).card : ENNReal) * (8 * (δ : ENNReal)) := by
    rw [Finset.sum_congr rfl fun j _ => Slab.volume_carrier (V j).toPrism3D,
      Finset.sum_const, nsmul_eq_mul]
  have hsum_density : (∑ j ∈ s with W j ≤ K, volume (V j).carrier)
      = densityIn s W K * volume K.carrier := by
    simpa [W] using (Kakeya.sum_volume_eq_densityIn_mul_volume s W K)
  have hdensity : densityIn s W K ≤ Δ := (Kakeya.le_maxDensity s W K).trans hΔ
  have hKvol : volume K.carrier = (4913 : ENNReal) * (8 * (θ : ENNReal)) := by
    change volume ((Slab.reslab (V i).toPrism3D θ hθ1).toPrismNDim.dilation 17).carrier
      = (4913 : ENNReal) * (8 * (θ : ENNReal))
    rw [PrismNDim.volume_dilation]
    norm_num
    change (4913 : ENNReal) * volume (Slab.reslab (V i).toPrism3D θ hθ1).carrier
      = (4913 : ENNReal) * (8 * (θ : ENNReal))
    rw [Slab.volume_carrier]
  calc
    ((angleCluster s V i (θ : ℝ)).card : ENNReal) * (8 * (δ : ENNReal))
        = ∑ j ∈ angleCluster s V i (θ : ℝ), volume (V j).carrier := hsum_cluster.symm
    _ ≤ ∑ j ∈ s with W j ≤ K, volume (V j).carrier := hsum_le
    _ = densityIn s W K * volume K.carrier := hsum_density
    _ ≤ Δ * volume K.carrier := by gcongr
    _ = Δ * ((4913 : ENNReal) * (8 * (θ : ENNReal))) := by rw [hKvol]

/-! ### The improved incidence bound -/

/-- **The pairwise incidence bound, in the `θ`-free form the cluster count consumes.**

For two `δ`-slabs whose plane angle is at least `θ - δ`, the shaded intersection satisfies
`|Y_i ∩ Y_j| · 8θ ≤ 320 δ ^ 2`.  This packages the two regimes of the pairwise estimate into one
division-free inequality: for `θ ≤ 5δ` it is the trivial bound `|Y_i ∩ Y_j| ≤ 8δ`, and for `θ > 5δ`
it is `Slab.volume_inter_le` at angle `θ - δ > 4θ/5`, i.e. `|S_i ∩ S_j| ≤ 32δ ^ 2 / (θ - δ) ≤
40 δ ^ 2 / θ`.  Multiplying by `8θ` is what makes the `θ`'s cancel against the cluster count. -/
theorem shade_inter_mul_le {θ : ℝ≥0} (hδ0 : 0 < δ) (hδθ : δ ≤ θ) (V : ι → ShadedSlab δ h) (i j : ι)
    (hang : (θ : ℝ) - δ ≤ Slab.angle (V i).toPrism3D (V j).toPrism3D) :
    volume ((V i).shade ∩ (V j).shade) * (8 * (θ : ENNReal)) ≤
      (320 : ENNReal) * (δ : ENNReal) ^ 2 := by
  have hδ_pos' : (0 : ℝ) < δ := by exact_mod_cast hδ0
  have hδ2 : (δ : ENNReal) ^ 2 = ENNReal.ofReal ((δ : ℝ) ^ 2) := by
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_pow δ.coe_nonneg]
  have h8θ : (8 : ENNReal) * (θ : ENNReal) = ENNReal.ofReal (8 * (θ : ℝ)) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8), ENNReal.ofReal_ofNat,
      ENNReal.ofReal_coe_nnreal]
  have hvol_carrier : volume ((V i).shade ∩ (V j).shade) ≤ volume (V i).carrier := by
    exact measure_mono (Set.inter_subset_left.trans (V i).shade_subset)
  have hvol8 : volume ((V i).shade ∩ (V j).shade) ≤ 8 * (δ : ENNReal) := by
    calc
      volume ((V i).shade ∩ (V j).shade) ≤ volume (V i).carrier := hvol_carrier
      _ = 8 * (δ : ENNReal) := Slab.volume_carrier (V i).toPrism3D
  rcases le_or_gt (θ : ℝ≥0) (5 * δ) with hcase | hcase
  · -- `θ ≤ 5δ`: the trivial bound `|Y_i ∩ Y_j| ≤ 8δ`
    have hθ5 : (θ : ENNReal) ≤ 5 * (δ : ENNReal) := by exact_mod_cast hcase
    calc
      volume ((V i).shade ∩ (V j).shade) * (8 * (θ : ENNReal))
          ≤ (8 * (δ : ENNReal)) * (8 * (θ : ENNReal)) := by
              simpa [mul_comm, mul_assoc] using mul_le_mul_right hvol8 (8 * (θ : ENNReal))
      _ = 64 * (δ : ENNReal) * (θ : ENNReal) := by ring
      _ ≤ 64 * (δ : ENNReal) * (5 * (δ : ENNReal)) := by
              simpa [mul_comm, mul_assoc] using mul_le_mul_left hθ5 (64 * (δ : ENNReal))
      _ = 320 * (δ : ENNReal) ^ 2 := by ring_nf
  · -- `5δ < θ`: `Slab.volume_inter_le` at angle `θ - δ`
    have hcase' : (5 : ℝ) * δ < (θ : ℝ) := by exact_mod_cast hcase
    have hθ5_le : (5 * (δ : ℝ) ≤ (θ : ℝ)) := le_of_lt hcase'
    have hθδ_pos : 0 < (θ : ℝ) - δ := by nlinarith [hδ_pos', hcase']
    have h_subset : ((V i).shade ∩ (V j).shade) ⊆
        (((V i).toPrism3D.carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩
          (V j).toPrism3D.carrier) :=
      Set.inter_subset_inter (V i).shade_subset (V j).shade_subset
    have h_pair := Slab.volume_inter_le (V i).toPrism3D (V j).toPrism3D hθδ_pos hang
    have h32 : volume ((V i).shade ∩ (V j).shade) ≤
        (Slab.volume_inter_le.C : ENNReal) * (δ : ENNReal) ^ 2 /
          ENNReal.ofReal ((θ : ℝ) - δ) := by
      exact (measure_mono h_subset).trans h_pair
    have h32f : (Slab.volume_inter_le.C : ENNReal) * (δ : ENNReal) ^ 2 /
          ENNReal.ofReal ((θ : ℝ) - δ) =
        ENNReal.ofReal (32 * (δ : ℝ) ^ 2 / ((θ : ℝ) - δ)) := by
      have hC : (Slab.volume_inter_le.C : ENNReal) = ENNReal.ofReal 32 := by
        rw [← ENNReal.ofReal_coe_nnreal]; norm_num [Slab.volume_inter_le.C]
      rw [hC, hδ2, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 32),
        ← ENNReal.ofReal_div_of_pos hθδ_pos]
    have h32f_nonneg : (0 : ℝ) ≤ 32 * (δ : ℝ) ^ 2 / ((θ : ℝ) - δ) :=
      div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 32) (sq_nonneg (δ : ℝ)))
        (le_of_lt hθδ_pos)
    calc
      volume ((V i).shade ∩ (V j).shade) * (8 * (θ : ENNReal))
          ≤ ((Slab.volume_inter_le.C : ENNReal) * (δ : ENNReal) ^ 2 /
                ENNReal.ofReal ((θ : ℝ) - δ)) * (8 * (θ : ENNReal)) := by
              simpa [mul_comm, mul_assoc] using mul_le_mul_right h32 (8 * (θ : ENNReal))
      _ = ENNReal.ofReal ((32 * (δ : ℝ) ^ 2 / ((θ : ℝ) - δ)) * (8 * (θ : ℝ))) := by
              rw [h32f, h8θ, ← ENNReal.ofReal_mul h32f_nonneg]
      _ ≤ (320 : ENNReal) * (δ : ENNReal) ^ 2 := by
              rw [hδ2]
              have h320 : (320 : ENNReal) = ENNReal.ofReal (320 : ℝ) := by norm_num
              rw [h320, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 320)]
              apply ENNReal.ofReal_le_ofReal
              have hA_nonneg : (0 : ℝ) ≤ 32 * (δ : ℝ) ^ 2 / ((θ : ℝ) - δ) :=
                div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 32) (sq_nonneg (δ : ℝ)))
                  (le_of_lt hθδ_pos)
              have h8θ_le : (8 * (θ : ℝ)) ≤ 10 * ((θ : ℝ) - δ) := by nlinarith [hθ5_le]
              calc
                (32 * (δ : ℝ) ^ 2 / ((θ : ℝ) - δ)) * (8 * (θ : ℝ))
                    ≤ (32 * (δ : ℝ) ^ 2 / ((θ : ℝ) - δ)) * (10 * ((θ : ℝ) - δ)) :=
                        mul_le_mul_of_nonneg_left h8θ_le hA_nonneg
                _ = 320 * (δ : ℝ) ^ 2 := by
                      have hθδ_ne : (θ : ℝ) - δ ≠ 0 := ne_of_gt hθδ_pos
                      field_simp [hθδ_ne]
                      ring

/-- **Only the cluster contributes.**  In the `i`-th inner sum of `ShadedSlab.triAtAngle`, the terms
whose carrier misses that of `V i` vanish, so the sum may be taken over `ShadedSlab.angleCluster`. -/
theorem sum_angleCluster_eq_sum_window {θ : ℝ≥0} (s : Finset ι) (V : ι → ShadedSlab δ h) (i : ι) :
    (∑ j ∈ angleCluster s V i (θ : ℝ), volume ((V i).shade ∩ (V j).shade)) =
      ∑ j ∈ s with (θ : ℝ) - δ ≤ Slab.angle (V i).toPrism3D (V j).toPrism3D ∧
          Slab.angle (V i).toPrism3D (V j).toPrism3D ≤ 2 * (θ : ℝ),
        volume ((V i).shade ∩ (V j).shade) := by
  refine Finset.sum_subset ?_ ?_
  · intro j hj
    simp only [angleCluster, Finset.mem_filter] at hj ⊢
    exact ⟨hj.1, hj.2.1⟩
  · intro j hj hnot
    simp only [angleCluster, Finset.mem_filter] at hj hnot
    have hempty : ((V i).carrier ∩ (V j).carrier : Set (EuclideanSpace ℝ (Fin 3))) = ∅ := by
      rw [← Set.not_nonempty_iff_eq_empty]
      intro hne
      exact hnot ⟨hj.1, ⟨⟨hj.2.1, hj.2.2⟩, hne⟩⟩
    refine measure_mono_null ?_ (measure_empty (μ := volume))
    calc ((V i).shade ∩ (V j).shade : Set (EuclideanSpace ℝ (Fin 3)))
        ⊆ ((V i).carrier ∩ (V j).carrier : Set (EuclideanSpace ℝ (Fin 3))) :=
          Set.inter_subset_inter (V i).shade_subset (V j).shade_subset
      _ = ∅ := hempty

/-- **The cluster sum against the pairwise bound.**  Multiply by `8θ` and apply
`ShadedSlab.shade_inter_mul_le` term by term. -/
theorem sum_angleCluster_mul_le {θ : ℝ≥0} (hδ0 : 0 < δ) (hδθ : δ ≤ θ) (s : Finset ι)
    (V : ι → ShadedSlab δ h) (i : ι) :
    (∑ j ∈ angleCluster s V i (θ : ℝ), volume ((V i).shade ∩ (V j).shade)) *
        (8 * (θ : ENNReal)) ≤
      ((angleCluster s V i (θ : ℝ)).card : ENNReal) * ((320 : ENNReal) * (δ : ENNReal) ^ 2) := by
  rw [Finset.sum_mul]
  calc
    (∑ j ∈ angleCluster s V i (θ : ℝ),
        volume ((V i).shade ∩ (V j).shade) * (8 * (θ : ENNReal)))
        ≤ ∑ j ∈ angleCluster s V i (θ : ℝ), (320 : ENNReal) * (δ : ENNReal) ^ 2 := by
          refine Finset.sum_le_sum ?_
          intro j hj
          have hj' : j ∈ s ∧ (θ - δ ≤ Slab.angle (V i).toPrism3D (V j).toPrism3D ∧
              Slab.angle (V i).toPrism3D (V j).toPrism3D ≤ 2 * (θ : ℝ)) ∧
              ((V i).carrier ∩ (V j).carrier : Set (EuclideanSpace ℝ (Fin 3))).Nonempty := by
            simpa [angleCluster] using hj
          exact shade_inter_mul_le hδ0 hδθ V i j hj'.2.1.1
    _ = ((angleCluster s V i (θ : ℝ)).card : ENNReal) *
        ((320 : ENNReal) * (δ : ENNReal) ^ 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]

/-- **The incidence bound at a typical angle, for a single slab of the family.**

`∑_{j : angle(i,j) ∈ [θ-δ, 2θ]} |Y_i ∩ Y_j| ≤ 196520 · Δ · δ`: the terms with disjoint carriers
vanish, the surviving ones form `ShadedSlab.angleCluster`, whose cardinality is controlled by
`ShadedSlab.card_angleCluster_mul_le`, and each contributes at most `320 δ ^ 2 / 8θ` by
`ShadedSlab.shade_inter_mul_le`. -/
theorem inner_incidence_le {θ : ℝ≥0} (hθ1 : θ ≤ 1) (s : Finset ι) (V : ι → ShadedSlab δ h)
    (hδ0 : 0 < δ) (hδθ : δ ≤ θ) {Δ : ENNReal}
    (hΔ : maxDensity s (fun j => (V j).toConvexSpaceBody) ≤ Δ) (i : ι) :
    (∑ j ∈ s with (θ : ℝ) - δ ≤ Slab.angle (V i).toPrism3D (V j).toPrism3D ∧
        Slab.angle (V i).toPrism3D (V j).toPrism3D ≤ 2 * (θ : ℝ),
      volume ((V i).shade ∩ (V j).shade)) ≤ (196520 : ENNReal) * Δ * (δ : ENNReal) := by
  classical
  rw [← sum_angleCluster_eq_sum_window s V i]
  let c : ENNReal := ((angleCluster s V i (θ : ℝ)).card : ENNReal)
  have hA8 : (∑ j ∈ angleCluster s V i (θ : ℝ), volume ((V i).shade ∩ (V j).shade)) *
        (8 * (θ : ENNReal)) ≤ c * ((320 : ENNReal) * (δ : ENNReal) ^ 2) := by
    dsimp [c]
    exact sum_angleCluster_mul_le hδ0 hδθ s V i
  have hcard : c * (8 * (δ : ENNReal)) ≤ Δ * ((4913 : ENNReal) * (8 * (θ : ENNReal))) := by
    dsimp [c]
    exact card_angleCluster_mul_le hθ1 s V hδθ hΔ i
  -- multiply by the nonzero finite factor `(8θ)·(8δ)`
  have hmain :
      (∑ j ∈ angleCluster s V i (θ : ℝ), volume ((V i).shade ∩ (V j).shade)) *
          ((8 * (θ : ENNReal)) * (8 * (δ : ENNReal))) ≤
        (196520 : ENNReal) * Δ * (δ : ENNReal) *
          ((8 * (θ : ENNReal)) * (8 * (δ : ENNReal))) := by
    calc
      (∑ j ∈ angleCluster s V i (θ : ℝ), volume ((V i).shade ∩ (V j).shade)) *
          ((8 * (θ : ENNReal)) * (8 * (δ : ENNReal)))
          = ((∑ j ∈ angleCluster s V i (θ : ℝ),
              volume ((V i).shade ∩ (V j).shade)) * (8 * (θ : ENNReal))) * (8 * (δ : ENNReal)) := by
            ring
      _ ≤ (c * ((320 : ENNReal) * (δ : ENNReal) ^ 2)) * (8 * (δ : ENNReal)) := by
            exact mul_le_mul_left hA8 (8 * (δ : ENNReal))
      _ = (c * (8 * (δ : ENNReal))) * ((320 : ENNReal) * (δ : ENNReal) ^ 2) := by ring
      _ ≤ (Δ * ((4913 : ENNReal) * (8 * (θ : ENNReal)))) *
            ((320 : ENNReal) * (δ : ENNReal) ^ 2) := by
            exact mul_le_mul_left hcard ((320 : ENNReal) * (δ : ENNReal) ^ 2)
      _ = (196520 : ENNReal) * Δ * (δ : ENNReal) *
            ((8 * (θ : ENNReal)) * (8 * (δ : ENNReal))) := by ring
  -- cancel the common factor `(8θ)·(8δ)`
  have hθ0 : 0 < θ := lt_of_lt_of_le hδ0 hδθ
  have h8θne0 : (8 * (θ : ENNReal)) ≠ 0 :=
    mul_ne_zero (by norm_num) (ENNReal.coe_ne_zero.mpr (ne_of_gt hθ0))
  have h8θneTop : (8 * (θ : ENNReal)) ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) ENNReal.coe_ne_top
  have h8δne0 : (8 * (δ : ENNReal)) ≠ 0 :=
    mul_ne_zero (by norm_num) (ENNReal.coe_ne_zero.mpr hδ0.ne')
  have h8δneTop : (8 * (δ : ENNReal)) ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) ENNReal.coe_ne_top
  have hfac_ne : (8 * (θ : ENNReal)) * (8 * (δ : ENNReal)) ≠ 0 :=
    mul_ne_zero h8θne0 h8δne0
  have hfac_top : (8 * (θ : ENNReal)) * (8 * (δ : ENNReal)) ≠ ⊤ :=
    ENNReal.mul_ne_top h8θneTop h8δneTop
  exact (ENNReal.mul_le_mul_iff_left hfac_ne hfac_top).mp hmain

/-- The absolute constant of `ShadedSlab.triAtAngle_le_maxDensity_mul`: the dilation loss `17 ^ 3`
of the cluster count times the constant `40` of the pairwise slab-intersection bound (which also
covers the small-angle regime `θ ≤ 5δ`, where the trivial bound `|S_i ∩ S_j| ≤ 8δ` is used). -/
noncomputable abbrev triAtAngle_le_maxDensity_mul.C : ℝ≥0 := 196520

/-- **The `Δ_max`-improved incidence bound at a typical angle.**

`Tri_θ(𝒮, Y) ≤ C · Δ · |s| · δ` for a family of `δ`-slabs with `Δ_max ≤ Δ`, whenever `δ ≤ θ ≤ 1`.

Compare `ShadedSlab.triAtAngle_le_card_sq_theta`, which gives `40 |s| ^ 2 δ ^ 2 / θ` with no
hypothesis on the family: the two agree when `|s| δ ≈ θ`, and this one is better exactly when the
family does not concentrate.  The `θ`-dependence cancels: the cluster count is proportional to
`θ / δ` and the pairwise intersection to `δ ^ 2 / θ`. -/
theorem triAtAngle_le_maxDensity_mul {θ : ℝ≥0} (hθ1 : θ ≤ 1) (s : Finset ι)
    (V : ι → ShadedSlab δ h) (hδ0 : 0 < δ) (hδθ : δ ≤ θ) {Δ : ENNReal}
    (hΔ : maxDensity s (fun j => (V j).toConvexSpaceBody) ≤ Δ) :
    triAtAngle s V (θ : ℝ) ≤
      (triAtAngle_le_maxDensity_mul.C : ENNReal) * Δ * (s.card : ENNReal) * (δ : ENNReal) := by
  rw [triAtAngle_def]
  calc
    (∑ i ∈ s, ∑ j ∈ s with (θ : ℝ) - δ ≤ Slab.angle (V i).toPrism3D (V j).toPrism3D ∧
        Slab.angle (V i).toPrism3D (V j).toPrism3D ≤ 2 * (θ : ℝ),
        volume ((V i).shade ∩ (V j).shade)) ≤
        ∑ i ∈ s, (196520 : ENNReal) * Δ * (δ : ENNReal) := by
      refine Finset.sum_le_sum ?_
      intro i hi
      exact inner_incidence_le hθ1 s V hδ0 hδθ hΔ i
    _ = (s.card : ENNReal) * ((196520 : ENNReal) * Δ * (δ : ENNReal)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ = (triAtAngle_le_maxDensity_mul.C : ENNReal) * Δ * (s.card : ENNReal) * (δ : ENNReal) := by
      simp [triAtAngle_le_maxDensity_mul.C]
      ring

/-! ### The `L ^ 2` multiplicity identity -/

/-- **The `L ^ 2` step, in multiplicity form.**  Cauchy--Schwarz on `f = ∑ 1_{Y_i}` says
`(∑ |Y_i|) ^ 2 ≤ |U| · Tri`, i.e. `μ · ∑ |Y_i| ≤ Tri`; combined with the typical-angle hypothesis
this reads `μ · ∑ |Y_i| ≤ M · Tri_θ`.  No slab geometry is used, only
`ShadedSlab.sum_shade_sq_le_union_mul_triAtAngle`. -/
theorem multiplicity_mul_sum_shade_le (s : Finset ι) (V : ι → ShadedSlab δ h)
    (θ : ℝ) (M : ENNReal) (h_typ : IsTypicalIntersectionAngle s V θ M) :
    ShadedBody.multiplicity s (fun i => (V i).toShadedBody) *
        (∑ i ∈ s, volume (V i).shade) ≤ M * triAtAngle s V θ := by
  by_cases hU0 : volume (⋃ i ∈ s, (V i).shade) = 0
  · have hS0 : (∑ i ∈ s, volume (V i).shade) = 0 :=
      Finset.sum_eq_zero fun i hi => measure_mono_null
        (fun x hx => Set.mem_iUnion₂.mpr ⟨i, hi, hx⟩) hU0
    rw [hS0]
    simp
  · rw [← ENNReal.mul_le_mul_iff_left hU0
        (ShadedBody.volume_iUnion_shade_ne_top s (fun i => (V i).toShadedBody))]
    calc
      (ShadedBody.multiplicity s (fun i => (V i).toShadedBody) *
          (∑ i ∈ s, volume (V i).shade)) * volume (⋃ i ∈ s, (V i).shade)
          = (∑ i ∈ s, volume (V i).shade) *
              (ShadedBody.multiplicity s (fun i => (V i).toShadedBody) *
                volume (⋃ i ∈ s, (V i).shade)) := by
              ring
      _ = (∑ i ∈ s, volume (V i).shade) * (∑ i ∈ s, volume (V i).shade) := by
          rw [ShadedBody.multiplicity_mul_union s (fun i => (V i).toShadedBody)]
      _ = (∑ i ∈ s, volume (V i).shade) ^ 2 := by rw [pow_two]
      _ ≤ M * volume (⋃ i ∈ s, (V i).shade) * triAtAngle s V θ :=
          sum_shade_sq_le_union_mul_triAtAngle s V θ M h_typ
      _ = (M * triAtAngle s V θ) * volume (⋃ i ∈ s, (V i).shade) := by ring

/-! ### GWZ Lemma 6.9 -/

/-- The absolute constant of GWZ Lemma 6.9, as formalised here: the incidence constant
`ShadedSlab.triAtAngle_le_maxDensity_mul.C = 196520` divided by the slab volume normalisation `8`. -/
noncomputable abbrev slabMultiplicity.C : ℝ≥0 := 24565

/-- **GWZ Lemma 6.9, multiplicity half.**

Let `𝒮 = (V i)_{i ∈ s}` be a nonempty family of `δ × 1 × 1` slabs with shading `Y`, let `θ ∈ [δ, 1]`
be an `M`-typical intersection angle for `(𝒮, Y)`, suppose `Δ_max(𝒮) ≤ Δ`, and let `lam` be a lower
bound for the fullness `λ(𝒮, Y)`.  Then

`μ(𝒮, Y) · 8 · lam ≤ 196520 · M · Δ`.

The chain is: `μ · ∑|Y_i| ≤ M · Tri_θ` (the `L ^ 2` step), `∑|Y_i| = λ |s| 8δ ≥ lam |s| 8δ` (the
shading-mass identity) and `Tri_θ ≤ C Δ |s| δ` (the `Δ_max`-improved incidence bound); the common
factor `|s| δ` cancels.

Stated multiplicatively so that no `ENNReal` division appears; see
`ShadedSlab.multiplicity_le_of_typicalAngle` for the divided form and
`ShadedSlab.slabMultiplicityEstimate` for the paper's `δ`-power form. -/
theorem multiplicity_mul_le_of_typicalAngle {θ : ℝ≥0} (hθ1 : θ ≤ 1) (s : Finset ι)
    (V : ι → ShadedSlab δ h) (hδ0 : 0 < δ) (hδθ : δ ≤ θ) (hs : s.Nonempty)
    (M : ENNReal) (h_typ : IsTypicalIntersectionAngle s V (θ : ℝ) M)
    {Δ : ENNReal} (hΔ : maxDensity s (fun j => (V j).toConvexSpaceBody) ≤ Δ)
    {lam : ℝ≥0} (hlam : lam ≤ ShadedBody.fullness s (fun i => (V i).toShadedBody)) :
    ShadedBody.multiplicity s (fun i => (V i).toShadedBody) * (8 * (lam : ENNReal)) ≤
      (triAtAngle_le_maxDensity_mul.C : ENNReal) * M * Δ := by
  classical
  let μ := ShadedBody.multiplicity s (fun i => (V i).toShadedBody)
  let C : ENNReal := (triAtAngle_le_maxDensity_mul.C : ENNReal)
  -- the common factor `|s| · δ` is nonzero and finite, so it cancels
  have hQ_ne0 : (s.card : ENNReal) * (δ : ENNReal) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hs.card_pos.ne') (ENNReal.coe_ne_zero.mpr hδ0.ne')
  have hQ_neTop : (s.card : ENNReal) * (δ : ENNReal) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.coe_ne_top
  -- shading-mass lower bound: `lam · |s| · 8δ ≤ Σ`
  have hsum :
      (lam : ENNReal) * ((s.card : ENNReal) * (8 * (δ : ENNReal))) ≤
        ∑ i ∈ s, volume (V i).shade := by
    rw [sum_volume_shade_eq]
    exact mul_le_mul_left (by exact_mod_cast hlam) _
  have hL2 := multiplicity_mul_sum_shade_le s V (θ : ℝ) M h_typ
  have htrid := triAtAngle_le_maxDensity_mul hθ1 s V hδ0 hδθ hΔ
  have hmain : ((s.card : ENNReal) * (δ : ENNReal)) * (μ * (8 * (lam : ENNReal))) ≤
      ((s.card : ENNReal) * (δ : ENNReal)) * (C * M * Δ) := by
    calc
      ((s.card : ENNReal) * (δ : ENNReal)) * (μ * (8 * (lam : ENNReal)))
          = (μ * (8 * (lam : ENNReal))) * ((s.card : ENNReal) * (δ : ENNReal)) := by ring
      _ = μ * ((lam : ENNReal) * ((s.card : ENNReal) * (8 * (δ : ENNReal)))) := by ring
      _ ≤ μ * (∑ i ∈ s, volume (V i).shade) := mul_le_mul_right hsum _
      _ ≤ M * triAtAngle s V (θ : ℝ) := hL2
      _ ≤ M * (C * Δ * (s.card : ENNReal) * (δ : ENNReal)) := mul_le_mul_right htrid _
      _ = ((s.card : ENNReal) * (δ : ENNReal)) * (C * M * Δ) := by ring
  exact (ENNReal.mul_le_mul_iff_right hQ_ne0 hQ_neTop).mp hmain

/-- **GWZ Lemma 6.9, multiplicity half, divided form**: `μ(𝒮, Y) ≤ C · M · Δ / lam`. -/
theorem multiplicity_le_of_typicalAngle {θ : ℝ≥0} (hθ1 : θ ≤ 1) (s : Finset ι)
    (V : ι → ShadedSlab δ h) (hδ0 : 0 < δ) (hδθ : δ ≤ θ) (hs : s.Nonempty)
    (M : ENNReal) (h_typ : IsTypicalIntersectionAngle s V (θ : ℝ) M)
    {Δ : ENNReal} (hΔ : maxDensity s (fun j => (V j).toConvexSpaceBody) ≤ Δ)
    {lam : ℝ≥0} (hlam0 : 0 < lam)
    (hlam : lam ≤ ShadedBody.fullness s (fun i => (V i).toShadedBody)) :
    ShadedBody.multiplicity s (fun i => (V i).toShadedBody) ≤
      (slabMultiplicity.C : ENNReal) * M * Δ / (lam : ENNReal) := by
  rw [ENNReal.le_div_iff_mul_le
      (Or.inl (ne_of_gt (ENNReal.coe_pos.mpr hlam0)))
      (Or.inl (ENNReal.coe_ne_top : (lam : ENNReal) ≠ ∞))]
  have hC : (triAtAngle_le_maxDensity_mul.C : ENNReal) =
      8 * (slabMultiplicity.C : ENNReal) := by
    norm_num
  have h_mul := multiplicity_mul_le_of_typicalAngle hθ1 s V hδ0 hδθ hs M h_typ hΔ hlam
  rw [hC] at h_mul
  rw [(ENNReal.mul_le_mul_iff_left (by norm_num : (8 : ENNReal) ≠ 0)
      (by norm_num : (8 : ENNReal) ≠ ∞)).symm]
  simpa [mul_assoc, mul_comm, mul_left_comm] using h_mul

/-- **GWZ Lemma 6.9, union-volume half.**

Under the same hypotheses, `64 · lam ^ 2 · |s| · δ ≤ 196520 · M · Δ · |U(𝒮, Y)|`.

This is the `Δ_max`-improved companion of GWZ Lemma 6.8
(`ShadedSlab.fullness_sq_angle_le_volume_union`, which gives `lam ^ 2 θ ≤ 40 M |U|`): the factor
`θ` on the left is replaced by the total slab mass `|s| δ`, which is the strong form the paper's
second conclusion `|U(𝒮, Y)| ≥ δ ^ (8η)` needs (with `Δ ≲ C_F |s| δ` for a `C_F`-Frostman family the
mass factors cancel and one is left with `|U| ≳ lam ^ 2 / (M · C_F)`). -/
theorem sq_fullness_mul_le_volume_union {θ : ℝ≥0} (hθ1 : θ ≤ 1) (s : Finset ι)
    (V : ι → ShadedSlab δ h) (hδ0 : 0 < δ) (hδθ : δ ≤ θ)
    (M : ENNReal) (h_typ : IsTypicalIntersectionAngle s V (θ : ℝ) M)
    {Δ : ENNReal} (hΔ : maxDensity s (fun j => (V j).toConvexSpaceBody) ≤ Δ)
    {lam : ℝ≥0} (hlam : lam ≤ ShadedBody.fullness s (fun i => (V i).toShadedBody)) :
    (64 : ENNReal) * (lam : ENNReal) ^ 2 * (s.card : ENNReal) * (δ : ENNReal) ≤
      (triAtAngle_le_maxDensity_mul.C : ENNReal) * M * Δ *
        volume (⋃ i ∈ s, (V i).shade) := by
  rcases Finset.eq_empty_or_nonempty s with rfl | hs
  · simp
  · set S : ENNReal := ∑ i ∈ s, volume (V i).shade
    set U : ENNReal := volume (⋃ i ∈ s, (V i).shade)
    let C : ENNReal := (triAtAngle_le_maxDensity_mul.C : ENNReal)
    -- the shading-mass identity `∑|Y_i| = λ|s|8δ ≥ lam·|s|·8δ`
    have hlin : (lam : ENNReal) * ((s.card : ENNReal) * (8 * (δ : ENNReal))) ≤ S := by
      dsimp [S]
      rw [sum_volume_shade_eq]
      exact mul_le_mul_left (by exact_mod_cast hlam) ((s.card : ENNReal) * (8 * (δ : ENNReal)))
    -- square it
    have hsq :
        (64 : ENNReal) * (lam : ENNReal) ^ 2 * (s.card : ENNReal) ^ 2 *
            (δ : ENNReal) ^ 2 ≤ S ^ 2 := by
      have hp : ((lam : ENNReal) * ((s.card : ENNReal) * (8 * (δ : ENNReal)))) ^ 2 ≤ S ^ 2 :=
        ENNReal.pow_le_pow_left hlin
      rwa [show ((lam : ENNReal) * ((s.card : ENNReal) * (8 * (δ : ENNReal)))) ^ 2 =
            (64 : ENNReal) * (lam : ENNReal) ^ 2 * (s.card : ENNReal) ^ 2 * (δ : ENNReal) ^ 2
          from by ring] at hp
    -- Cauchy--Schwarz: `S ^ 2 ≤ M · U · Tri_θ`
    have hcu : S ^ 2 ≤ M * U * triAtAngle s V (θ : ℝ) := by
      dsimp [S, U]
      exact sum_shade_sq_le_union_mul_triAtAngle s V (θ : ℝ) M h_typ
    -- the `Δ_max`-improved incidence bound
    have htri := triAtAngle_le_maxDensity_mul hθ1 s V hδ0 hδθ hΔ
    have hle2 :
        (64 : ENNReal) * (lam : ENNReal) ^ 2 * (s.card : ENNReal) ^ 2 * (δ : ENNReal) ^ 2 ≤
          M * U * (C * Δ * (s.card : ENNReal) * (δ : ENNReal)) :=
      (hsq.trans hcu).trans (mul_le_mul_right htri (M * U))
    -- the common factor `|s|·δ` is nonzero and finite (cancellation below)
    have hQ_ne_zero : (s.card : ENNReal) * (δ : ENNReal) ≠ 0 :=
      mul_ne_zero (by exact_mod_cast hs.card_pos.ne') (ENNReal.coe_ne_zero.mpr hδ0.ne')
    have hQ_ne_top : (s.card : ENNReal) * (δ : ENNReal) ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.coe_ne_top
    rw [show (64 : ENNReal) * (lam : ENNReal) ^ 2 * (s.card : ENNReal) ^ 2 * (δ : ENNReal) ^ 2 =
          ((s.card : ENNReal) * (δ : ENNReal)) *
            (64 * (lam : ENNReal) ^ 2 * (s.card : ENNReal) * (δ : ENNReal)) from by ring,
      show M * U * (C * Δ * (s.card : ENNReal) * (δ : ENNReal)) =
          ((s.card : ENNReal) * (δ : ENNReal)) * (C * M * Δ * U) from by ring] at hle2
    exact (ENNReal.mul_le_mul_iff_right hQ_ne_zero hQ_ne_top).mp hle2

/-- **GWZ Lemma 6.9 in the paper's `δ`-power form.**

With fullness at least `δ ^ η`, `Δ_max(𝒮) ≤ δ ^ (-η)` and a typical-angle loss `M ≤ δ ^ (-η)`, the
multiplicity of a nonempty family of `δ`-slabs obeys

`μ(𝒮, Y) ≤ 24565 · δ ^ (-3η)`.

The paper states `μ(𝒮) ≲ δ ^ (-8η)`; the exponent here is `-3η`, which is stronger (`δ ≤ 1`), and
the loss is the single explicit absolute constant `24565`.  The paper's own hypotheses `b, c ≥ δ ^ η`
do not appear because they are the hypotheses of the general `δ × b × c` case: for `b = c = 1` they
are vacuous, and the general case follows by the linear change of variables which normalises the two
long axes (not formalised here). -/
theorem slabMultiplicityEstimate {θ : ℝ≥0} (hθ1 : θ ≤ 1) (s : Finset ι)
    (V : ι → ShadedSlab δ h) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hδθ : δ ≤ θ) (hs : s.Nonempty)
    {η : ℝ} (hη : 0 ≤ η) (M : ENNReal) (h_typ : IsTypicalIntersectionAngle s V (θ : ℝ) M)
    (hM : M ≤ (δ : ENNReal) ^ (-η))
    (hΔ : maxDensity s (fun j => (V j).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η))
    (hlam : (δ : ℝ≥0) ^ η ≤ ShadedBody.fullness s (fun i => (V i).toShadedBody)) :
    ShadedBody.multiplicity s (fun i => (V i).toShadedBody) ≤
      (slabMultiplicity.C : ENNReal) * (δ : ENNReal) ^ (-3 * η) := by
  let e : ENNReal := (δ : ENNReal)
  let C : ENNReal := (slabMultiplicity.C : ENNReal)
  have hδne : δ ≠ 0 := hδ0.ne'
  have hx0 : e ≠ 0 := by
    dsimp [e]
    exact ENNReal.coe_ne_zero.mpr hδne
  have hxtop : e ≠ ⊤ := by
    simp [e]
  have hMu :
      ShadedBody.multiplicity s (fun i => (V i).toShadedBody) ≤
        C * e ^ (-η) * e ^ (-η) / e ^ η := by
    calc
      ShadedBody.multiplicity s (fun i => (V i).toShadedBody)
          ≤ C * M * e ^ (-η) / e ^ η := by
            have hinst :=
              multiplicity_le_of_typicalAngle hθ1 s V hδ0 hδθ
                hs M h_typ (Δ := (δ : ENNReal) ^ (-η)) hΔ
                (lam := (δ : ℝ≥0) ^ η) (hlam0 := NNReal.rpow_pos hδ0) hlam
            rw [ENNReal.coe_rpow_of_ne_zero hδne] at hinst
            simpa [e, C] using hinst
      _ ≤ C * e ^ (-η) * e ^ (-η) / e ^ η := by
            apply ENNReal.div_le_div_right (c := e ^ η)
            gcongr
  have hprod : e ^ (-η) * e ^ (-η) = e ^ (-2 * η) := by
    rw [← ENNReal.rpow_add (-η) (-η) hx0 hxtop]
    congr 1
    ring
  have hquot : e ^ (-2 * η) / e ^ η = e ^ (-3 * η) := by
    rw [← ENNReal.rpow_sub (-2 * η) η hx0 hxtop]
    congr 1
    ring
  have hdivInv : (e ^ η)⁻¹ = e ^ (-η) := (ENNReal.rpow_neg e η).symm
  have hfull : C * e ^ (-η) * e ^ (-η) / e ^ η = C * e ^ (-3 * η) := by
    calc
      C * e ^ (-η) * e ^ (-η) / e ^ η
          = (C * (e ^ (-η) * e ^ (-η))) * (e ^ η)⁻¹ := by
            rw [mul_assoc, ENNReal.div_eq_inv_mul, mul_comm]
      _ = (C * (e ^ (-η) * e ^ (-η))) * e ^ (-η) := by rw [hdivInv]
      _ = C * ((e ^ (-η) * e ^ (-η)) * e ^ (-η)) := by rw [mul_assoc]
      _ = C * (e ^ (-2 * η) * e ^ (-η)) := by rw [hprod]
      _ = C * e ^ (-3 * η) := by
            rw [← ENNReal.rpow_add (-2 * η) (-η) hx0 hxtop]
            have hexp : (-2 * η) + (-η) = -3 * η := by ring
            rw [hexp]
  calc
    ShadedBody.multiplicity s (fun i => (V i).toShadedBody)
        ≤ C * e ^ (-η) * e ^ (-η) / e ^ η := hMu
    _ ≤ C * e ^ (-3 * η) := by rw [hfull]
    _ ≤ (slabMultiplicity.C : ENNReal) * (δ : ENNReal) ^ (-3 * η) := by
          simp [C, e]

/-! ### Existence of a typical intersection angle

GWZ Definition 6.7 records without proof that a family with `μ ≥ 2` always has a typical
intersection angle `θ ∈ [δ, 1]`, the loss `M` being the number of dyadic angle scales.  That
pigeonhole is what makes GWZ Lemma 6.9 a statement about `(𝒮, Y)` alone, with no `(θ, M)` datum, and
it is proved here.  The windows are `[θ_k - δ, 2θ_k]` for `θ_k = min 1 (2 ^ k δ)`; consecutive
windows overlap, the last one reaches `2 ≥ π/2`, and every plane angle lies in `[0, π/2]`.
-/

/-- The `k`-th dyadic test angle at resolution `δ`, capped at `1`. -/
def dyadicAngle (δ : ℝ≥0) (k : ℕ) : ℝ≥0 := min 1 (2 ^ k * δ)

/-- The number of dyadic angle windows needed to cover `[0, 2]` at resolution `δ`: two more than
`log₂ ⌈δ⁻¹⌉`, so that the last test angle is `1` and the last window is `[1 - δ, 2]`. -/
def numAngleWindows (δ : ℝ≥0) : ℕ := Nat.log 2 ⌈(δ : ℝ)⁻¹⌉₊ + 2

theorem le_dyadicAngle (hδ1 : δ ≤ 1) (k : ℕ) : δ ≤ dyadicAngle δ k := by
  rw [dyadicAngle]
  exact le_min hδ1 (le_mul_of_one_le_left (by positivity)
    (by exact one_le_pow₀ (by norm_num : (1 : ℝ≥0) ≤ 2)))

theorem dyadicAngle_le_one (δ : ℝ≥0) (k : ℕ) : dyadicAngle δ k ≤ 1 := min_le_left _ _

/-- **The windows cover `[0, 2]`.**  Every `x ∈ [0, 2]` — in particular every plane angle, which
lies in `[0, π/2]` — falls in one of the `numAngleWindows δ` windows `[θ_k - δ, 2θ_k]`. -/
theorem exists_dyadicAngle_window (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {x : ℝ} (hx0 : 0 ≤ x) (hx2 : x ≤ 2) :
    ∃ k < numAngleWindows δ,
      (dyadicAngle δ k : ℝ) - (δ : ℝ) ≤ x ∧ x ≤ 2 * (dyadicAngle δ k : ℝ) := by
  classical
  let N : ℕ := ⌈(δ : ℝ)⁻¹⌉₊
  let K : ℕ := Nat.log 2 N + 1
  -- `K < numAngleWindows δ`
  have hK_lt : K < numAngleWindows δ := by
    dsimp [K, N, numAngleWindows]
    omega
  -- the last test angle reaches `1`: `dyadicAngle δ K = 1`
  have hK_val : dyadicAngle δ K = (1 : ℝ≥0) := by
    have hNlog : N < 2 ^ K := by
      have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num : 1 < 2) N
      simpa [K] using h
    have hce : (δ : ℝ)⁻¹ ≤ (N : ℝ) := by
      dsimp [N]
      exact Nat.le_ceil ((δ : ℝ)⁻¹)
    have hδpos : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
    have hcc : (δ : ℝ)⁻¹ < (2 : ℝ) ^ K := by
      have hN : (N : ℝ) < (2 : ℝ) ^ K := by exact_mod_cast hNlog
      exact lt_of_le_of_lt hce hN
    have h1lt : (1 : ℝ) < (2 : ℝ) ^ K * (δ : ℝ) := by
      have hδne0 : (δ : ℝ) ≠ 0 := ne_of_gt hδpos
      calc
        (1 : ℝ) = (δ : ℝ) * (δ : ℝ)⁻¹ := by rw [mul_inv_cancel₀ hδne0]
        _ < (2 : ℝ) ^ K * (δ : ℝ) := by
          rw [mul_comm]
          exact mul_lt_mul_of_pos_right hcc hδpos
    have hmin : (1 : ℝ≥0) ≤ 2 ^ K * δ := by exact_mod_cast (le_of_lt h1lt)
    dsimp [dyadicAngle]
    exact min_eq_left hmin
  -- consecutive windows overlap: `dyadicAngle δ (m+1) ≤ 2 * dyadicAngle δ m`
  have hstep : ∀ m : ℕ, (dyadicAngle δ (m + 1) : ℝ) ≤ 2 * (dyadicAngle δ m : ℝ) := by
    intro m
    have harg : 2 * (2 ^ m * δ) = 2 ^ (m + 1) * δ := by
      rw [pow_succ]
      ring
    have hinv : 2 * min 1 (2 ^ m * δ) = min 2 (2 ^ (m + 1) * δ) := by
      rw [mul_min_of_nonneg (b := 1) (c := 2 ^ m * δ)
        (by norm_num : (0 : ℝ≥0) ≤ (2 : ℝ≥0))]
      rw [harg]
      norm_num
    have hle0 : (dyadicAngle δ (m + 1) : ℝ≥0) ≤ 2 * dyadicAngle δ m := by
      calc
        dyadicAngle δ (m + 1) = min 1 (2 ^ (m + 1) * δ) := rfl
        _ ≤ min 2 (2 ^ (m + 1) * δ) := by exact min_le_min (by norm_num) le_rfl
        _ = 2 * min 1 (2 ^ m * δ) := hinv.symm
        _ = 2 * dyadicAngle δ m := by rw [dyadicAngle]
    exact_mod_cast hle0
  -- take the least `k` with `x ≤ 2 * dyadicAngle δ k`
  let P : ℕ → Prop := fun k => x ≤ 2 * (dyadicAngle δ k : ℝ)
  have hPK : P K := by
    unfold P
    have hval : 2 * (dyadicAngle δ K : ℝ) = (2 : ℝ) := by rw [hK_val]; norm_num
    rw [hval]
    exact hx2
  have hPexists : ∃ n, P n := ⟨K, hPK⟩
  have hPk : P (Nat.find hPexists) := Nat.find_spec hPexists
  have hfk : Nat.find hPexists ≤ K := Nat.find_le hPK
  have hfk_lt : Nat.find hPexists < numAngleWindows δ := lt_of_le_of_lt hfk hK_lt
  have hlo : (dyadicAngle δ (Nat.find hPexists) : ℝ) - (δ : ℝ) ≤ x := by
    by_cases hf0 : Nat.find hPexists = 0
    · rw [hf0]
      have hdR : (dyadicAngle δ 0 : ℝ) = (δ : ℝ) := by
        have hd : dyadicAngle δ 0 = (δ : ℝ≥0) := by
          dsimp [dyadicAngle]
          have h01 : (2 ^ 0 * δ : ℝ≥0) ≤ 1 := by simpa using hδ1
          rw [min_eq_right h01]
          norm_num
        exact_mod_cast hd
      rw [hdR]
      simp only [sub_self]
      exact hx0
    · let m : ℕ := Nat.find hPexists - 1
      have hfind_eq : Nat.find hPexists = m + 1 := by
        dsimp [m]
        omega
      have hnotPm : ¬ P m := by
        intro hPm
        have hmm : Nat.find hPexists ≤ m := Nat.find_le hPm
        omega
      have hgt : 2 * (dyadicAngle δ m : ℝ) < x :=
        lt_of_not_ge (by simpa [P] using hnotPm)
      rw [hfind_eq]
      exact le_of_lt (by
        calc
          (dyadicAngle δ (m + 1) : ℝ) - (δ : ℝ) ≤ 2 * (dyadicAngle δ m : ℝ) := by
            have hδn0 : (0 : ℝ) ≤ (δ : ℝ) := by exact_mod_cast (le_of_lt hδ0)
            linarith [hstep m, hδn0]
          _ < x := hgt)
  refine ⟨Nat.find hPexists, hfk_lt, ?lu, ?ul⟩
  · exact hlo
  · simpa [P] using hPk

/-- The incidence mass is at most the sum of the windowed incidence masses: every pair falls in
some window. -/
theorem tri_le_sum_triAtAngle (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (s : Finset ι)
    (V : ι → ShadedSlab δ h) :
    tri s V ≤
      ∑ k ∈ Finset.range (numAngleWindows δ), triAtAngle s V (dyadicAngle δ k : ℝ) := by
  classical
  let f : ι → ι → ENNReal := fun i j => volume ((V i).shade ∩ (V j).shade)
  -- For a single `i`, every `j` falls in some dyadic window.
  have hmain : ∀ i, i ∈ s →
      (∑ j ∈ s, f i j) ≤
        ∑ k ∈ Finset.range (numAngleWindows δ),
          ∑ j ∈ s with
              (dyadicAngle δ k : ℝ) - (δ : ℝ) ≤ Slab.angle (V i).toPrism3D (V j).toPrism3D ∧
                Slab.angle (V i).toPrism3D (V j).toPrism3D ≤ 2 * (dyadicAngle δ k : ℝ),
            f i j := by
    intro i hi
    let W : ι → ℕ → Prop := fun j k =>
      (dyadicAngle δ k : ℝ) - (δ : ℝ) ≤ Slab.angle (V i).toPrism3D (V j).toPrism3D ∧
        Slab.angle (V i).toPrism3D (V j).toPrism3D ≤ 2 * (dyadicAngle δ k : ℝ)
    have hwin : ∀ j, j ∈ s → ∃ k, k ∈ Finset.range (numAngleWindows δ) ∧ W j k := by
      intro j hj
      rcases exists_dyadicAngle_window hδ0 hδ1
          (show 0 ≤ Slab.angle (V i).toPrism3D (V j).toPrism3D from
            Prism3D.angle_nonneg _ _)
          (show Slab.angle (V i).toPrism3D (V j).toPrism3D ≤ 2 from
            (Prism3D.angle_le_pi_div_two _ _).trans (by linarith [Real.pi_le_four]))
        with ⟨k, hklt, hk⟩
      exact ⟨k, Finset.mem_range.mpr hklt, hk⟩
    let kof : ι → ℕ := fun j => if hj : j ∈ s then (hwin j hj).choose else 0
    have hkof_range : ∀ j, j ∈ s → kof j ∈ Finset.range (numAngleWindows δ) := by
      intro j hj
      simpa [kof, hj] using (hwin j hj).choose_spec.1
    have hkof_win : ∀ j, j ∈ s → W j (kof j) := by
      intro j hj
      simpa [kof, hj] using (hwin j hj).choose_spec.2
    have hfib : (∑ j ∈ s, f i j) =
        ∑ k ∈ Finset.range (numAngleWindows δ),
            ∑ j ∈ s with kof j = k, f i j := by
      exact (Finset.sum_fiberwise_of_maps_to hkof_range (fun j => f i j)).symm
    have hsub : ∀ k, (s.filter (fun j => kof j = k)) ⊆ s.filter (fun j => W j k) := by
      intro k j hj
      rw [Finset.mem_filter] at hj ⊢
      exact ⟨hj.1, by
        have hk : kof j = k := hj.2
        rw [← hk]
        exact hkof_win j hj.1⟩
    calc
      (∑ j ∈ s, f i j) =
          ∑ k ∈ Finset.range (numAngleWindows δ), ∑ j ∈ s with kof j = k, f i j := hfib
      _ ≤ ∑ k ∈ Finset.range (numAngleWindows δ),
            ∑ j ∈ s with W j k, f i j := by
        refine Finset.sum_le_sum ?_
        intro k hk
        exact Finset.sum_le_sum_of_subset (hsub k)
  calc
    tri s V = ∑ i ∈ s, ∑ j ∈ s, f i j := by
      rw [tri_def]
    _ ≤ ∑ i ∈ s, ∑ k ∈ Finset.range (numAngleWindows δ),
          ∑ j ∈ s with
              (dyadicAngle δ k : ℝ) - (δ : ℝ) ≤ Slab.angle (V i).toPrism3D (V j).toPrism3D ∧
                Slab.angle (V i).toPrism3D (V j).toPrism3D ≤ 2 * (dyadicAngle δ k : ℝ),
            f i j := by
      refine Finset.sum_le_sum ?_
      intro i hi
      simpa [f] using hmain i hi
    _ = ∑ k ∈ Finset.range (numAngleWindows δ),
          triAtAngle s V (dyadicAngle δ k : ℝ) := by
      rw [Finset.sum_comm]
      simp [f, triAtAngle_def]

/-- **A typical intersection angle always exists** (GWZ Definition 6.7), with loss the number of
dyadic angle windows.  This is the ingredient that removes the `(θ, M)` datum from Lemma 6.9. -/
theorem exists_typicalIntersectionAngle (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (s : Finset ι)
    (V : ι → ShadedSlab δ h) :
    ∃ θ : ℝ≥0, δ ≤ θ ∧ θ ≤ 1 ∧
      IsTypicalIntersectionAngle s V (θ : ℝ) ((numAngleWindows δ : ℕ) : ENNReal) := by
  classical
  let N : ℕ := numAngleWindows δ
  -- the dyadic windows form a nonempty finite set of test angles
  have hNpos : 0 < N := by
    dsimp [N, numAngleWindows]
    omega
  have hN : (Finset.range N).Nonempty := ⟨0, Finset.mem_range.mpr hNpos⟩
  -- some window maximises the windowed incidence mass
  obtain ⟨k₀, _hk₀, hmax⟩ := Finset.exists_max_image (Finset.range N)
    (fun k => triAtAngle s V (dyadicAngle δ k : ℝ)) hN
  -- the total incidence mass is bounded by `N` times the maximal window
  have hsum : tri s V ≤ (N : ENNReal) * triAtAngle s V (dyadicAngle δ k₀ : ℝ) := by
    calc
      tri s V ≤ ∑ k ∈ Finset.range N, triAtAngle s V (dyadicAngle δ k : ℝ) := by
        simpa [N] using tri_le_sum_triAtAngle hδ0 hδ1 s V
      _ ≤ (Finset.range N).card • triAtAngle s V (dyadicAngle δ k₀ : ℝ) :=
        Finset.sum_le_card_nsmul (Finset.range N)
          (fun k => triAtAngle s V (dyadicAngle δ k : ℝ))
          (triAtAngle s V (dyadicAngle δ k₀ : ℝ)) hmax
      _ = (N : ENNReal) * triAtAngle s V (dyadicAngle δ k₀ : ℝ) := by
        rw [Finset.card_range, nsmul_eq_mul]
  refine ⟨dyadicAngle δ k₀, le_dyadicAngle hδ1 k₀, dyadicAngle_le_one δ k₀, ?_⟩
  exact hsum

/-! ### GWZ Lemma 6.9, paper-facing form -/

/-- **GWZ Lemma 6.9** in the form the paper states it: for a nonempty family of shaded `δ × 1 × 1`
slabs with `Δ_max(𝒮) ≤ Δ` and fullness at least `lam`,

`μ(𝒮, Y) · 8 · lam ≤ 196520 · (number of dyadic angle windows) · Δ`.

No typical-angle datum appears: it is supplied by
`ShadedSlab.exists_typicalIntersectionAngle`.  The only loss beyond the absolute constant is the
number of dyadic angle windows, which is `O(log δ⁻¹)` and therefore sub-polynomial — see
`ShadedSlab.exists_delta0_multiplicity_mul_le` for the absorbed form. -/
theorem multiplicity_mul_le_of_maxDensity (s : Finset ι) (V : ι → ShadedSlab δ h)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hs : s.Nonempty)
    {Δ : ENNReal} (hΔ : maxDensity s (fun j => (V j).toConvexSpaceBody) ≤ Δ)
    {lam : ℝ≥0} (hlam : lam ≤ ShadedBody.fullness s (fun i => (V i).toShadedBody)) :
    ShadedBody.multiplicity s (fun i => (V i).toShadedBody) * (8 * (lam : ENNReal)) ≤
      (triAtAngle_le_maxDensity_mul.C : ENNReal) * ((numAngleWindows δ : ℕ) : ENNReal) * Δ := by
  obtain ⟨θ, hδθ, hθ1, h_typ⟩ := exists_typicalIntersectionAngle hδ0 hδ1 s V
  exact multiplicity_mul_le_of_typicalAngle hθ1 s V hδ0 hδθ hs _ h_typ hΔ hlam

/-- The real-valued form of the sub-polynomial window count: `log₂ ⌈δ⁻¹⌉ + 2 ≤ K · δ ^ (-ε)`. -/
theorem exists_numAngleWindows_le_real {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ((Nat.log 2 ⌈δ⁻¹⌉₊ : ℝ) + 2) ≤ K * δ ^ (-ε) := by
  obtain ⟨K₀, hK₀⟩ := Kakeya.logarg_subpoly (M := 2) (N := 1) (r := 2) (by norm_num) hε
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hNatLog : ∀ n : ℕ, (Nat.log 2 n : ℝ) ≤ Real.log n / Real.log 2 := by
    intro n
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simp
    · rw [le_div_iff₀ hlog2]
      have h1 : (2 : ℝ) ^ Nat.log 2 n ≤ n := by exact_mod_cast Nat.pow_log_le_self 2 (by omega)
      have h2 := Real.log_le_log (by positivity) h1
      rwa [Real.log_pow] at h2
  refine ⟨max K₀ 0, le_max_right _ _, ?_⟩
  intro δ hδ0 hδ1
  let x : ℝ := (⌈δ⁻¹⌉₊ : ℝ)
  have hx0 : 0 ≤ x := by
    dsimp [x]
    exact Nat.cast_nonneg _
  have hxle : x ≤ 2 * δ ^ (-1 : ℝ) := by
    have hδpos : 0 < (δ : ℝ)⁻¹ := inv_pos.mpr hδ0
    have hceil : (⌈δ⁻¹⌉₊ : ℝ) < δ⁻¹ + 1 := Nat.ceil_lt_add_one (le_of_lt hδpos)
    have hinv1 : (1 : ℝ) ≤ δ⁻¹ := one_le_inv_iff₀.mpr ⟨hδ0, hδ1⟩
    have hsum : δ⁻¹ + 1 ≤ 2 * δ⁻¹ := by nlinarith
    have hxle' : (⌈δ⁻¹⌉₊ : ℝ) ≤ 2 * δ⁻¹ := le_of_lt (lt_of_lt_of_le hceil hsum)
    dsimp [x]
    simpa [Real.rpow_neg_one] using hxle'
  have hmain : Real.log x / Real.log 2 + 2 ≤ K₀ * δ ^ (-ε) :=
    hK₀ δ x hδ0 hδ1 hx0 hxle
  have hstep : ((Nat.log 2 ⌈δ⁻¹⌉₊ : ℝ) + 2) ≤ Real.log x / Real.log 2 + 2 := by
    dsimp [x]
    linarith [hNatLog ⌈δ⁻¹⌉₊]
  have hrpow0 : 0 ≤ δ ^ (-ε) := Real.rpow_nonneg (le_of_lt hδ0) (-ε)
  have hlast : K₀ * δ ^ (-ε) ≤ max K₀ 0 * δ ^ (-ε) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hrpow0
  exact le_trans (le_trans hstep hmain) hlast

/-- **The window count is sub-polynomial.**  `numAngleWindows δ = O(log δ⁻¹)`, so for every `ε > 0`
there is a `δ`-independent constant `K` with `numAngleWindows δ ≤ K · δ ^ (-ε)`. -/
theorem exists_numAngleWindows_le {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ≥0, ∀ δ : ℝ≥0, 0 < δ → δ ≤ 1 →
      ((numAngleWindows δ : ℕ) : ENNReal) ≤ (K : ENNReal) * (δ : ENNReal) ^ (-ε) := by
  obtain ⟨K₀, hK₀nn, hK₀⟩ := exists_numAngleWindows_le_real hε
  let K : ℝ≥0 := ⟨K₀, hK₀nn⟩
  refine ⟨K, fun δ hδ0 hδ1 => ?_⟩
  have hδR0 : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
  have hδR1 : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ1
  have hreal : ((Nat.log 2 ⌈(δ : ℝ)⁻¹⌉₊ : ℝ) + 2) ≤ K₀ * (δ : ℝ) ^ (-ε) :=
    hK₀ (δ : ℝ) hδR0 hδR1
  have hN : ((numAngleWindows δ : ℕ) : ℝ) = (Nat.log 2 ⌈(δ : ℝ)⁻¹⌉₊ : ℝ) + 2 := by
    simp [numAngleWindows]
  have hL : ((numAngleWindows δ : ℕ) : ENNReal)
      = ENNReal.ofReal ((numAngleWindows δ : ℕ) : ℝ) := by
    simp
  have hRK : (K : ENNReal) = ENNReal.ofReal K₀ := by
    dsimp [K]
    exact (ENNReal.ofReal_eq_coe_nnreal hK₀nn).symm
  have hRd : (δ : ENNReal) ^ (-ε) = ENNReal.ofReal ((δ : ℝ) ^ (-ε)) := by
    rw [← ENNReal.ofReal_rpow_of_pos hδR0]
    simp
  have hR : (K : ENNReal) * (δ : ENNReal) ^ (-ε)
      = ENNReal.ofReal (K₀ * (δ : ℝ) ^ (-ε)) := by
    rw [hRK, hRd]
    exact (ENNReal.ofReal_mul hK₀nn).symm
  rw [hL, hR]
  exact ENNReal.ofReal_le_ofReal (by rw [hN]; exact hreal)

/-- **Constant absorption threshold** (the local copy of the `rpow` absorption used downstream):
for `C : ℝ≥0` and `0 < e` there is `δ₀ > 0` with `C ≤ δ ^ (-e)` for all `0 < δ ≤ δ₀`. -/
theorem exists_delta0_const_le_rpow (C : ℝ≥0) {e : ℝ} (he : 0 < e) :
    ∃ δ₀ : ℝ≥0, 0 < δ₀ ∧ ∀ δ : ℝ≥0, 0 < δ → δ ≤ δ₀ →
      (C : ENNReal) ≤ (δ : ENNReal) ^ (-e) := by
  -- use `D = max C 1`, which is `≥ 1`, to avoid the `C = 0` edge case
  let D : ℝ≥0 := max C 1
  have hD1 : 1 ≤ D := le_max_right C 1
  have hD0 : 0 < D := lt_of_lt_of_le (by norm_num : (0 : ℝ≥0) < 1) hD1
  have hD0_ne : D ≠ 0 := hD0.ne'
  have hC_le_D : C ≤ D := le_max_left C 1
  have he_ne : e ≠ 0 := by linarith
  set δ₀ : ℝ≥0 := D ^ (-1 / e)
  have hδ₀_pos : 0 < δ₀ := NNReal.rpow_pos hD0
  refine ⟨δ₀, hδ₀_pos, ?_⟩
  intro δ hδ hδle
  -- lift δ ≤ δ₀ to ENNReal
  have hδle_coe : (δ : ENNReal) ≤ (δ₀ : ENNReal) := by exact_mod_cast hδle
  have hD_enn_ne0 : (D : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hD0_ne
  have hD_enn_ne_top : (D : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  -- Step 1: `(δ₀ : ENNReal) ^ (-e) = (D : ENNReal)`
  have h_eq : (δ₀ : ENNReal) ^ (-e) = (D : ENNReal) := by
    calc
      (δ₀ : ENNReal) ^ (-e) = ((D : ENNReal) ^ (-1 / e)) ^ (-e) := by
        rw [← ENNReal.coe_rpow_of_ne_zero hD0_ne (-1 / e)]
      _ = (D : ENNReal) ^ ((-1 / e) * (-e)) := by rw [ENNReal.rpow_mul]
      _ = (D : ENNReal) ^ (1 : ℝ) := by field_simp [he_ne]
      _ = (D : ENNReal) := by simp
  -- Step 2: monotonicity of `x ↦ x ^ e` for `e > 0`, then invert
  have h_e_nonneg : 0 ≤ e := by linarith
  have h_pow_e : (δ : ENNReal) ^ e ≤ (δ₀ : ENNReal) ^ e :=
    ENNReal.rpow_le_rpow hδle_coe h_e_nonneg
  have h_inv : ((δ₀ : ENNReal) ^ e)⁻¹ ≤ ((δ : ENNReal) ^ e)⁻¹ :=
    (ENNReal.inv_le_inv.mpr h_pow_e)
  calc
    (C : ENNReal) ≤ (D : ENNReal) := by exact_mod_cast hC_le_D
    _ = (δ₀ : ENNReal) ^ (-e) := by rw [h_eq]
    _ = ((δ₀ : ENNReal) ^ e)⁻¹ := by rw [ENNReal.rpow_neg]
    _ ≤ ((δ : ENNReal) ^ e)⁻¹ := h_inv
    _ = (δ : ENNReal) ^ (-e) := by rw [ENNReal.rpow_neg]

/-- **GWZ Lemma 6.9, absorbed form.**  For every `ε > 0` there is a threshold `δ₀` below which both
the absolute constant and the logarithmic window count of
`ShadedSlab.multiplicity_mul_le_of_maxDensity` are absorbed into `δ ^ (-ε)`:

`μ(𝒮, Y) · lam ≤ δ ^ (-ε) · Δ`.

This is the shape the Section-6 large-`b` branches consume. -/
theorem exists_delta0_multiplicity_mul_le {ε : ℝ} (hε : 0 < ε) :
    ∃ δ₀ : ℝ≥0, 0 < δ₀ ∧
      ∀ {ι : Type*} {δ : ℝ≥0} {h : δ ≤ 1} (s : Finset ι) (V : ι → ShadedSlab δ h),
        0 < δ → δ ≤ δ₀ → s.Nonempty →
        ∀ {Δ : ENNReal}, maxDensity s (fun j => (V j).toConvexSpaceBody) ≤ Δ →
        ∀ {lam : ℝ≥0}, lam ≤ ShadedBody.fullness s (fun i => (V i).toShadedBody) →
          ShadedBody.multiplicity s (fun i => (V i).toShadedBody) * (lam : ENNReal) ≤
            (δ : ENNReal) ^ (-ε) * Δ := by
  have hε2 : 0 < ε / 2 := by nlinarith
  rcases exists_numAngleWindows_le (ε := ε / 2) hε2 with ⟨K, hK⟩
  rcases exists_delta0_const_le_rpow (24565 * K) (e := ε / 2) hε2 with ⟨δ₀c, hδ₀c_pos, hδ₀c⟩
  let δ₀ : ℝ≥0 := min δ₀c 1
  refine ⟨δ₀, ?_, ?_⟩
  · dsimp [δ₀]
    exact lt_min_iff.mpr ⟨hδ₀c_pos, by norm_num⟩
  · intro ι δ _h s V hδ0 hδ₀le hs Δ hΔ lam hlam
    dsimp [δ₀] at hδ₀le
    have hδ₀c_le : δ ≤ δ₀c := le_trans hδ₀le (min_le_left _ _)
    have hle1 : δ ≤ 1 := le_trans hδ₀le (min_le_right _ _)
    let μ : ENNReal := ShadedBody.multiplicity s (fun i => (V i).toShadedBody)
    let nw : ENNReal := (numAngleWindows δ : ℕ)
    let δPow : ENNReal := (δ : ENNReal) ^ (-(ε / 2))
    have hδne0 : (δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hδ0.ne'
    have hδneTop : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
    have hwin : nw ≤ (K : ENNReal) * δPow := by
      dsimp [nw, δPow]
      exact hK δ hδ0 hle1
    have hconst : (24565 * K : ENNReal) ≤ δPow := by
      dsimp [δPow]
      simpa [ENNReal.coe_mul] using hδ₀c δ hδ0 hδ₀c_le
    have hA : μ * (8 * (lam : ENNReal)) ≤ (196520 : ENNReal) * nw * Δ := by
      simpa [μ, nw, triAtAngle_le_maxDensity_mul.C] using
        (multiplicity_mul_le_of_maxDensity s V hδ0 hle1 hs hΔ hlam)
    have hmain : (8 : ENNReal) * (μ * (lam : ENNReal)) ≤
        (8 : ENNReal) * ((24565 * K : ENNReal) * δPow * Δ) := by
      calc
        (8 : ENNReal) * (μ * (lam : ENNReal)) = μ * (8 * (lam : ENNReal)) := by ring
        _ ≤ (196520 : ENNReal) * nw * Δ := hA
        _ ≤ (196520 : ENNReal) * ((K : ENNReal) * δPow) * Δ := by
            gcongr
        _ = (8 : ENNReal) * ((24565 * K : ENNReal) * δPow * Δ) := by
            have hcen : (196520 : ENNReal) = (8 : ENNReal) * (24565 : ENNReal) := by norm_num
            rw [hcen]
            simp [mul_assoc, mul_comm, mul_left_comm]
    have hstep : μ * (lam : ENNReal) ≤ ((24565 * K : ENNReal) * δPow) * Δ :=
      (ENNReal.mul_le_mul_iff_right (by norm_num : (8 : ENNReal) ≠ 0)
        (by norm_num : (8 : ENNReal) ≠ ⊤)).mp hmain
    have hfinal : ((24565 * K : ENNReal) * δPow) * Δ ≤ δPow * δPow * Δ := by
      have hm : (24565 * K : ENNReal) * δPow ≤ δPow * δPow :=
        mul_le_mul hconst le_rfl (by positivity) (by positivity)
      exact mul_le_mul hm le_rfl (by positivity) (by positivity)
    have hpow : δPow * δPow = (δ : ENNReal) ^ (-ε) := by
      dsimp [δPow]
      rw [← ENNReal.rpow_add (-(ε / 2)) (-(ε / 2)) hδne0 hδneTop]
      congr 1
      ring
    calc
      μ * (lam : ENNReal) ≤ ((24565 * K : ENNReal) * δPow) * Δ := hstep
      _ ≤ δPow * δPow * Δ := hfinal
      _ = (δ : ENNReal) ^ (-ε) * Δ := by rw [hpow]

end ShadedSlab

/-! ### Widening a shaded plank family to a shaded slab family

An `a × b × 1` plank sits inside the `a × 1 × 1` slab with the same centre and frame
(`Plank.toSlab`).  Widening a *shaded* plank family this way keeps the shading, hence keeps the
multiplicity exactly, and costs only the factor `b` in the fullness and in the maximal density.  For
`b` bounded below — which is exactly the large-`b` regime of GWZ Proposition 6.6 — those factors are
absolute constants, and Lemma 6.9 applies to the widened family.
-/

namespace ShadedPlank

variable {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {ι : Type*}

/-- The `a × 1 × 1` slab about a shaded `a × b × 1` plank, carrying the same shading. -/
def toShadedSlab (ha1 : a ≤ 1) (W : ShadedPlank a b hab hb1) : ShadedSlab a ha1 where
  __ := W.plank.toSlab a ha1
  shade := W.shade
  measurableSet_shade := W.measurableSet_shade
  shade_subset := W.shade_subset.trans (Plank.subset_toSlab W.plank le_rfl ha1)

@[simp] theorem toShadedSlab_shade (ha1 : a ≤ 1) (W : ShadedPlank a b hab hb1) :
    (W.toShadedSlab ha1).shade = W.shade := rfl

/-- Widening does not change the multiplicity: multiplicity sees only the shadings. -/
theorem multiplicity_toShadedSlab (ha1 : a ≤ 1) (s : Finset ι)
    (W : ι → ShadedPlank a b hab hb1) :
    ShadedBody.multiplicity s (fun j => ((W j).toShadedSlab ha1).toShadedBody) =
      ShadedBody.multiplicity s (fun j => (W j).toShadedBody) := by
  simp [ShadedBody.multiplicity_eq_div]

/-- Widening costs exactly the factor `b` in the fullness. -/
theorem fullness_toShadedSlab_ge (ha1 : a ≤ 1) (ha0 : 0 < a) (hb0 : 0 < b) (s : Finset ι)
    (W : ι → ShadedPlank a b hab hb1) :
    b * ShadedBody.fullness s (fun j => (W j).toShadedBody) ≤
      ShadedBody.fullness s (fun j => ((W j).toShadedSlab ha1).toShadedBody) := by
  rcases Finset.eq_empty_or_nonempty s with rfl | hs
  · simp [ShadedBody.fullness]
  · rw [← ENNReal.coe_le_coe]
    rw [ENNReal.coe_mul]
    rw [ShadedBody.fullness_def]
    rw [ShadedBody.fullness_def]
    let X : ENNReal := ∑ j ∈ s, volume (W j).shade
    let C : ENNReal := (s.card : ENNReal) * (8 * (a : ENNReal))
    have hXp : (∑ j ∈ s, volume ((W j).toShadedBody).shade) = X := by
      dsimp [X]
    have hXs : (∑ j ∈ s, volume (((W j).toShadedSlab ha1).toShadedBody).shade) = X := by
      dsimp [X]
    have hDp : (∑ j ∈ s, volume ((W j).toShadedBody).carrier) = C * (b : ENNReal) := by
      rw [Finset.sum_congr rfl (fun j _ => ShadedPlank.volume_carrier (W j)),
        Finset.sum_const, nsmul_eq_mul]
      dsimp [C]
      ring
    have hDs : (∑ j ∈ s, volume (((W j).toShadedSlab ha1).toShadedBody).carrier) = C := by
      rw [Finset.sum_congr rfl (fun j hj => by
        have hv : volume (((W j).toShadedSlab ha1).carrier) = 8 * (a : ENNReal) := by
          rw [show ((((W j).toShadedSlab ha1).carrier : Set (EuclideanSpace ℝ (Fin 3))) =
                  ((W j).plank.toSlab a ha1).carrier) from rfl]
          exact Plank.volume_toSlab (W j).plank a ha1
        simpa using hv), Finset.sum_const, nsmul_eq_mul]
    rw [hXp, hXs, hDp, hDs]
    have hb0e : (b : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hb0.ne'
    have hbTop : (b : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
    have hC0 : C ≠ 0 := by
      refine mul_ne_zero ?_ ?_
      · exact_mod_cast hs.card_pos.ne'
      · exact mul_ne_zero (by norm_num) (ENNReal.coe_ne_zero.mpr ha0.ne')
    have hdiv : X / (C * (b : ENNReal)) = (X / C) / (b : ENNReal) := by
      have h := ENNReal.mul_div_mul_comm (a := X) (b := 1) (c := C) (d := (b : ENNReal))
        (Or.inl hC0) (Or.inr hb0e)
      simpa [div_eq_mul_inv] using h
    have hident : (b : ENNReal) * (X / (C * (b : ENNReal))) = X / C := by
      rw [hdiv]
      exact (ENNReal.mul_div_cancel hb0e hbTop : (b : ENNReal) * ((X / C) / (b : ENNReal)) = X / C)
    rw [hident]

/-- Widening costs at most the factor `b` in the maximal density: a widened slab contained in a test
body contains its plank, and the plank has `b` times the volume. -/
theorem maxDensity_toShadedSlab_le (ha1 : a ≤ 1) (hb0 : 0 < b) (s : Finset ι)
    (W : ι → ShadedPlank a b hab hb1) {Δ : ENNReal}
    (hΔ : maxDensity s (fun j => (W j).toConvexSpaceBody) ≤ Δ) :
    maxDensity s (fun j => ((W j).toShadedSlab ha1).toConvexSpaceBody) ≤ Δ / (b : ENNReal) := by
  classical
  let B : ι → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) :=
    fun j => ((W j).toShadedSlab ha1).toConvexSpaceBody
  let P : ι → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) :=
    fun j => (W j).toConvexSpaceBody
  -- the plank is contained in its widened slab
  have hPB : ∀ j, P j ≤ B j := by
    intro j
    change (P j : Set (EuclideanSpace ℝ (Fin 3))) ⊆ (B j : Set (EuclideanSpace ℝ (Fin 3)))
    change (((W j).toConvexSpaceBody) : Set (EuclideanSpace ℝ (Fin 3))) ⊆
      (((W j).toShadedSlab ha1).toConvexSpaceBody : Set (EuclideanSpace ℝ (Fin 3)))
    change (W j).plank.carrier ⊆ ((W j).plank.toSlab a ha1).carrier
    exact Plank.subset_toSlab (W j).plank le_rfl ha1
  have hb0' : (b : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hb0.ne'
  have hbtop : (b : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  change Kakeya.maxDensity s B ≤ Δ / (b : ENNReal)
  rw [Kakeya.maxDensity_le_iff]
  intro K
  change Kakeya.densityIn s B K ≤ Δ / (b : ENNReal)
  rw [ENNReal.le_div_iff_mul_le (Or.inl hb0') (Or.inl hbtop)]
  -- the widened slab has volume `8 · a`; the plank `8 · a · b`
  have hslab_vol : ∀ j, volume (B j).carrier = 8 * (a : ENNReal) := by
    intro j
    dsimp [B]
    rw [show (((W j).toShadedSlab ha1).toConvexSpaceBody).carrier =
        ((W j).plank.toSlab a ha1).carrier from rfl]
    exact Slab.volume_carrier ((W j).plank.toSlab a ha1)
  have hplank_vol : ∀ j, volume (P j).carrier = 8 * (a : ENNReal) * (b : ENNReal) := by
    intro j
    dsimp [P]
    rw [show (((W j).toConvexSpaceBody).carrier) = ((W j).plank).carrier from rfl]
    rw [Prism3D.volume_carrier (W j).plank]
    simp [mul_assoc]
  have hbvol : ∀ j, (b : ENNReal) * volume (B j).carrier = volume (P j).carrier := by
    intro j
    rw [hslab_vol j, hplank_vol j]
    ring
  have hmain : (b : ENNReal) * Kakeya.densityIn s B K ≤ Kakeya.densityIn s P K := by
    let X : ENNReal := ∑ j ∈ s with B j ≤ K, volume (B j).carrier
    let Y : ENNReal := ∑ j ∈ s with B j ≤ K, volume (P j).carrier
    let Z : ENNReal := ∑ j ∈ s with P j ≤ K, volume (P j).carrier
    let v : ENNReal := volume K.carrier
    -- the subfamily of widened slabs contained in `K` is contained in that of planks
    have hsub : (s.filter (fun j => B j ≤ K)) ⊆ s.filter (fun j => P j ≤ K) := by
      intro j hj
      rw [Finset.mem_filter] at hj ⊢
      exact ⟨hj.1, (hPB j).trans hj.2⟩
    have hbX : (b : ENNReal) * X = Y := by
      dsimp [X, Y]
      rw [Finset.mul_sum, Finset.sum_congr rfl (fun j hj => hbvol j)]
    have hYleZ : Y ≤ Z := by
      dsimp [Y, Z]
      exact Finset.sum_le_sum_of_subset hsub
    have ht : (b : ENNReal) * (X / v) = ((b : ENNReal) * X) / v := by
      calc
        (b : ENNReal) * (X / v) = (b : ENNReal) * (X * v⁻¹) := by rw [div_eq_mul_inv]
        _ = ((b : ENNReal) * X) * v⁻¹ := by rw [← mul_assoc]
        _ = ((b : ENNReal) * X) / v := by rw [div_eq_mul_inv]
    calc
      (b : ENNReal) * Kakeya.densityIn s B K
          = (b : ENNReal) * (X / v) := by rfl
      _ = ((b : ENNReal) * X) / v := ht
      _ = Y / v := by rw [hbX]
      _ ≤ Z / v := by
            rw [div_eq_mul_inv]
            exact mul_le_mul_left hYleZ (v)⁻¹
      _ = Kakeya.densityIn s P K := by rfl
  have hbound : (b : ENNReal) * Kakeya.densityIn s B K ≤ Δ :=
    hmain.trans ((Kakeya.le_maxDensity s P K).trans hΔ)
  simpa [mul_comm] using hbound

/-! ### The large-`b` outer plank bound

This is the form in which GWZ Proposition 6.6 consumes Lemma 6.9 (paper, page 22): when the outer
plank width `b` is too large for the plank estimates of Lemmas 6.1/6.4, the outer family
`𝒲 = (W j)_{j ∈ ts}` of `a × b × 1` planks is treated as a family of `a × 1 × 1` *slabs* — widening
costs only the factor `b`, bounded below in this regime — and Lemma 6.9 bounds its multiplicity by
`Δ_max / λ` up to the logarithmic window count.  With the Katz--Tao and fullness data
`Δ_max(𝒲) ≤ a ^ (-η)`, `λ(𝒲) ≥ a ^ η` this is sub-polynomial.
-/

/-- **The outer plank multiplicity bound at large `b`.**  For a nonempty family of shaded
`a × b × 1` planks with `b₀ ≤ b`, `Δ_max(𝒲) ≤ d ^ (-η)` and `λ(𝒲) ≥ d ^ η`,

`μ(𝒲, Y) · (b₀ ^ 2 · 8) ≤ 196520 · K · d ^ (-(ε + 2η))`,

where `K` is any constant bounding the window count `numAngleWindows` by `K · a ^ (-ε)` (supplied by
`ShadedSlab.exists_numAngleWindows_le`).  The two factors of `d ^ (-η)` come from the maximal density
and from the fullness; the factor `b ^ 2 ≥ b₀ ^ 2` is the widening loss, once from the density and
once from the fullness.

The density and fullness data are read at an auxiliary scale `d ≤ a` rather than at the plank scale
`a` itself.  Both readings are needed: Section 6 has them at the master scale `δ ≤ ρ ≤ a` and never
at `a` (see `Kakeya.PlankEstimateAtMasterScale` for why the plank-scale reading is not available
after GWZ Proposition 5.1), whereas the plank-scale reading is the case `d = a`.  Only the window
count stays at `a`, and `a ^ (-ε) ≤ d ^ (-ε)` absorbs the difference. -/
theorem multiplicity_le_of_isKatzTao_of_large {ε : ℝ} {K b₀ : ℝ≥0} (hb₀ : 0 < b₀)
    (hK : ∀ δ' : ℝ≥0, 0 < δ' → δ' ≤ 1 →
      ((ShadedSlab.numAngleWindows δ' : ℕ) : ENNReal) ≤ (K : ENNReal) * (δ' : ENNReal) ^ (-ε))
    {κ' : Type*} (ts : Finset κ') {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (W : κ' → ShadedPlank a b hab hb1) (ha0 : 0 < a) (hbb₀ : b₀ ≤ b) (hts : ts.Nonempty)
    {d : ℝ≥0} (hd0 : 0 < d) (hda : d ≤ a) (hε0 : 0 ≤ ε)
    {η : ℝ} (hη : 0 < η)
    (hKT : maxDensity ts (fun j => (W j).toConvexSpaceBody) ≤ (d : ENNReal) ^ (-η))
    (hfull : (d : ℝ≥0) ^ η ≤ ShadedBody.fullness ts (fun j => (W j).toShadedBody)) :
    ShadedBody.multiplicity ts (fun j => (W j).toShadedBody) * ((b₀ : ENNReal) ^ 2 * 8) ≤
      (196520 : ENNReal) * (K : ENNReal) * (d : ENNReal) ^ (-(ε + 2 * η)) := by
  have ha1 : a ≤ 1 := hab.trans hb1
  have hb0 : 0 < b := lt_of_lt_of_le hb₀ hbb₀
  set μ : ENNReal := ShadedBody.multiplicity ts (fun j => (W j).toShadedBody) with hμ
  let lam : ℝ≥0 := b * d ^ η
  let nw : ENNReal := ((ShadedSlab.numAngleWindows a : ℕ) : ENNReal)
  have hηpos : (0 : ℝ) < η := hη
  have hde0 : (d : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hd0.ne'
  have hdetop : (d : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hbe0 : (b : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hb0.ne'
  have hbetop : (b : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  -- fullness of the widened family is at least `b * d ^ η`
  have hlamE : (lam : ENNReal) = (b : ENNReal) * (d : ENNReal) ^ η := by
    change ((b * d ^ η : ℝ≥0) : ENNReal) = (b : ENNReal) * (d : ENNReal) ^ η
    rw [ENNReal.coe_mul]
    rw [ENNReal.coe_rpow_of_ne_zero hd0.ne']
  have hfull_e : (d : ENNReal) ^ η ≤
      (ShadedBody.fullness ts (fun j => (W j).toShadedBody) : ENNReal) := by
    rw [← ENNReal.coe_rpow_of_ne_zero hd0.ne']
    exact_mod_cast hfull
  have hlam_EN : (lam : ENNReal) ≤
      (ShadedBody.fullness ts (fun j => ((W j).toShadedSlab ha1).toShadedBody) : ENNReal) := by
    calc
      (lam : ENNReal) = (b : ENNReal) * (d : ENNReal) ^ η := hlamE
      _ ≤ (b : ENNReal) * (ShadedBody.fullness ts (fun j => (W j).toShadedBody) : ENNReal) := by
          exact mul_le_mul_right hfull_e (b : ENNReal)
      _ ≤ (ShadedBody.fullness ts (fun j => ((W j).toShadedSlab ha1).toShadedBody) : ENNReal) := by
          exact_mod_cast (fullness_toShadedSlab_ge ha1 ha0 hb0 ts W)
  have hlam : lam ≤ ShadedBody.fullness ts (fun j => ((W j).toShadedSlab ha1).toShadedBody) :=
    ENNReal.coe_le_coe.mp hlam_EN
  -- the maximal density of the widened family is at most `d ^ (-η) / b`
  have hΔ : maxDensity ts (fun j => ((W j).toShadedSlab ha1).toConvexSpaceBody) ≤
      (d : ENNReal) ^ (-η) / (b : ENNReal) := by
    exact maxDensity_toShadedSlab_le ha1 hb0 ts W hKT
  -- GWZ Lemma 6.9 on the widened family
  have h69raw := ShadedSlab.multiplicity_mul_le_of_maxDensity ts (fun j => (W j).toShadedSlab ha1)
    ha0 ha1 hts (hΔ := hΔ) (lam := lam) hlam
  have h69 : μ * (8 * (lam : ENNReal)) ≤
      (196520 : ENNReal) * nw * ((d : ENNReal) ^ (-η) / (b : ENNReal)) := by
    rw [hμ]
    rw [← ShadedPlank.multiplicity_toShadedSlab ha1 ts W]
    dsimp [nw]
    exact h69raw
  -- multiply by `b` and clear the division
  have hb_mul : (b : ENNReal) * (μ * (8 * (((b : ENNReal) * (d : ENNReal) ^ η)))) ≤
      (b : ENNReal) * ((196520 : ENNReal) * nw * ((d : ENNReal) ^ (-η) / (b : ENNReal))) := by
    rw [hlamE] at h69
    exact mul_le_mul_right h69 (b : ENNReal)
  have hLb : (b : ENNReal) * (μ * (8 * (((b : ENNReal) * (d : ENNReal) ^ η)))) =
      μ * (8 * (b : ENNReal) ^ 2 * (d : ENNReal) ^ η) := by ring
  have hRb : (b : ENNReal) * ((196520 : ENNReal) * nw * ((d : ENNReal) ^ (-η) / (b : ENNReal))) =
      (196520 : ENNReal) * nw * (d : ENNReal) ^ (-η) := by
    calc
      (b : ENNReal) * ((196520 : ENNReal) * nw * ((d : ENNReal) ^ (-η) / (b : ENNReal)))
          = (196520 : ENNReal) * nw * (b * ((d : ENNReal) ^ (-η) / (b : ENNReal))) := by ring
      _ = (196520 : ENNReal) * nw * (d : ENNReal) ^ (-η) := by
          rw [ENNReal.mul_div_cancel hbe0 hbetop]
  have hmain : μ * (8 * (b : ENNReal) ^ 2 * (d : ENNReal) ^ η) ≤
      (196520 : ENNReal) * nw * (d : ENNReal) ^ (-η) := by
    rw [hLb, hRb] at hb_mul
    exact hb_mul
  -- bound the logarithmic window count, at the plank scale `a`
  have hKwin : nw ≤ (K : ENNReal) * (a : ENNReal) ^ (-ε) := by
    dsimp [nw]
    exact hK a ha0 ha1
  -- `a ^ (-ε) ≤ d ^ (-ε)` since `d ≤ a` and `ε ≥ 0`
  have hdaE : (d : ENNReal) ≤ (a : ENNReal) := by exact_mod_cast hda
  have hap_le : (a : ENNReal) ^ (-ε) ≤ (d : ENNReal) ^ (-ε) := by
    rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
    exact ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow hdaE hε0)
  have hKwin' : nw ≤ (K : ENNReal) * (d : ENNReal) ^ (-ε) := by
    calc
      nw ≤ (K : ENNReal) * (a : ENNReal) ^ (-ε) := hKwin
      _ ≤ (K : ENNReal) * (d : ENNReal) ^ (-ε) := by
          simpa [mul_comm] using (mul_le_mul_left hap_le (K : ENNReal))
  have h69c : μ * (8 * (b : ENNReal) ^ 2 * (d : ENNReal) ^ η) ≤
      (196520 : ENNReal) * (K : ENNReal) * (d : ENNReal) ^ (-ε) * (d : ENNReal) ^ (-η) := by
    calc
      μ * (8 * (b : ENNReal) ^ 2 * (d : ENNReal) ^ η)
          ≤ (196520 : ENNReal) * nw * (d : ENNReal) ^ (-η) := hmain
      _ = nw * ((196520 : ENNReal) * (d : ENNReal) ^ (-η)) := by ring
      _ ≤ (K : ENNReal) * (d : ENNReal) ^ (-ε) * ((196520 : ENNReal) * (d : ENNReal) ^ (-η)) := by
          exact mul_le_mul_left hKwin' ((196520 : ENNReal) * (d : ENNReal) ^ (-η))
      _ = (196520 : ENNReal) * (d : ENNReal) ^ (-η) *
              ((K : ENNReal) * (d : ENNReal) ^ (-ε)) := by ring
      _ = (196520 : ENNReal) * (K : ENNReal) * (d : ENNReal) ^ (-ε) *
              (d : ENNReal) ^ (-η) := by ring
  -- exponent bookkeeping: pull the factor `d ^ η` out of both sides
  have hprod1 : (d : ENNReal) ^ (-ε) * (d : ENNReal) ^ (-η) = (d : ENNReal) ^ (-(ε + η)) := by
    rw [← ENNReal.rpow_add (-ε) (-η) hde0 hdetop]
    congr 1
    ring
  have hprod2 :
      (d : ENNReal) ^ (-(ε + η)) = (d : ENNReal) ^ (-(ε + 2 * η)) * (d : ENNReal) ^ η := by
    rw [← ENNReal.rpow_add (-(ε + 2 * η)) η hde0 hdetop]
    congr 1
    ring
  have hcoeff : (196520 : ENNReal) * (K : ENNReal) * (d : ENNReal) ^ (-ε) * (d : ENNReal) ^ (-η) =
      (196520 : ENNReal) * (K : ENNReal) * (d : ENNReal) ^ (-(ε + 2 * η)) * (d : ENNReal) ^ η := by
    calc
      (196520 : ENNReal) * (K : ENNReal) * (d : ENNReal) ^ (-ε) * (d : ENNReal) ^ (-η)
          = (196520 : ENNReal) * (K : ENNReal) *
              ((d : ENNReal) ^ (-ε) * (d : ENNReal) ^ (-η)) := by ring
      _ = (196520 : ENNReal) * (K : ENNReal) * (d : ENNReal) ^ (-(ε + η)) := by rw [hprod1]
      _ = (196520 : ENNReal) * (K : ENNReal) *
              ((d : ENNReal) ^ (-(ε + 2 * η)) * (d : ENNReal) ^ η) := by rw [hprod2]
      _ = (196520 : ENNReal) * (K : ENNReal) * (d : ENNReal) ^ (-(ε + 2 * η)) *
              (d : ENNReal) ^ η := by ring
  have hLHS : μ * (8 * (b : ENNReal) ^ 2 * (d : ENNReal) ^ η) =
      (μ * (8 * (b : ENNReal) ^ 2)) * (d : ENNReal) ^ η := by ring
  have htgt : μ * (8 * (b : ENNReal) ^ 2) ≤
      (196520 : ENNReal) * (K : ENNReal) * (d : ENNReal) ^ (-(ε + 2 * η)) := by
    have hane0 : (d : ENNReal) ^ η ≠ 0 := by
      simp [hde0, hdetop]
    have hanet : (d : ENNReal) ^ η ≠ ⊤ := ENNReal.rpow_ne_top_of_ne_zero hde0 hdetop
    rw [hcoeff, hLHS] at h69c
    exact (ENNReal.mul_le_mul_iff_left hane0 hanet).mp h69c
  -- weaken `b ^ 2` to `b₀ ^ 2`
  have hbb2 : (b₀ : ENNReal) ^ 2 ≤ (b : ENNReal) ^ 2 :=
    ENNReal.pow_le_pow_left (by exact_mod_cast hbb₀)
  calc
    μ * ((b₀ : ENNReal) ^ 2 * 8) = μ * (8 * (b₀ : ENNReal) ^ 2) := by ring
    _ ≤ μ * (8 * (b : ENNReal) ^ 2) := by gcongr
    _ ≤ (196520 : ENNReal) * (K : ENNReal) * (d : ENNReal) ^ (-(ε + 2 * η)) := htgt

/-- **The large-`b` outer plank bound, division form.**
`ShadedPlank.multiplicity_le_of_isKatzTao_of_large` with the absolute factor `b₀ ^ 2 · 8` moved to
the right-hand side, which is the shape the Section-6 fallbacks consume. -/
theorem multiplicity_le_of_isKatzTao_of_large' {ε : ℝ} {K b₀ : ℝ≥0} (hb₀ : 0 < b₀)
    (hK : ∀ δ' : ℝ≥0, 0 < δ' → δ' ≤ 1 →
      ((ShadedSlab.numAngleWindows δ' : ℕ) : ENNReal) ≤ (K : ENNReal) * (δ' : ENNReal) ^ (-ε))
    {κ' : Type*} (ts : Finset κ') {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (W : κ' → ShadedPlank a b hab hb1) (ha0 : 0 < a) (hbb₀ : b₀ ≤ b) (hts : ts.Nonempty)
    {d : ℝ≥0} (hd0 : 0 < d) (hda : d ≤ a) (hε0 : 0 ≤ ε)
    {η : ℝ} (hη : 0 < η)
    (hKT : maxDensity ts (fun j => (W j).toConvexSpaceBody) ≤ (d : ENNReal) ^ (-η))
    (hfull : (d : ℝ≥0) ^ η ≤ ShadedBody.fullness ts (fun j => (W j).toShadedBody)) :
    ShadedBody.multiplicity ts (fun j => (W j).toShadedBody) ≤
      ((196520 * K * (8 * b₀ ^ 2)⁻¹ : ℝ≥0) : ENNReal) * (d : ENNReal) ^ (-(ε + 2 * η)) := by
  let μ := ShadedBody.multiplicity ts (fun j => (W j).toShadedBody)
  let X : ENNReal := (d : ENNReal) ^ (-(ε + 2 * η))
  let c : ENNReal := (b₀ : ENNReal) ^ 2 * 8
  let r : ENNReal := (8 * (b₀ : ENNReal) ^ 2)⁻¹
  let C : ENNReal := ((196520 * K * (8 * b₀ ^ 2)⁻¹ : ℝ≥0) : ENNReal)
  have h := multiplicity_le_of_isKatzTao_of_large hb₀ hK ts W ha0 hbb₀ hts hd0 hda hε0 hη hKT hfull
  -- h : μ * ((b₀ : ENNReal) ^ 2 * 8) ≤ (196520 : ENNReal) * (K : ENNReal) * X
  have hb2ne0 : 8 * (b₀ : ENNReal) ^ 2 ≠ 0 := by positivity
  have hb2top : 8 * (b₀ : ENNReal) ^ 2 ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by norm_num : (8 : ENNReal) ≠ ⊤)
      (ENNReal.pow_ne_top (by exact ENNReal.coe_ne_top : (b₀ : ENNReal) ≠ ⊤))
  have hc0 : c ≠ 0 := by
    dsimp [c]
    positivity
  have hctop : c ≠ ⊤ := by
    dsimp [c]
    exact ENNReal.mul_ne_top
      (ENNReal.pow_ne_top (by exact ENNReal.coe_ne_top : (b₀ : ENNReal) ≠ ⊤))
      (by norm_num : (8 : ENNReal) ≠ ⊤)
  -- (8 * (b₀ : ENNReal) ^ 2)⁻¹ * ((b₀ : ENNReal) ^ 2 * 8) = 1
  have hrinv : r * ((b₀ : ENNReal) ^ 2 * 8) = 1 := by
    dsimp [r]
    have hm : 8 * (b₀ : ENNReal) ^ 2 = (b₀ : ENNReal) ^ 2 * 8 := by ring
    rw [← hm]
    exact ENNReal.inv_mul_cancel hb2ne0 hb2top
  -- the ℝ≥0 constant coerces to the ENNReal product
  have hcoepush : ((8 * b₀ ^ 2 : ℝ≥0) : ENNReal) = 8 * (b₀ : ENNReal) ^ 2 := by
    rw [ENNReal.coe_mul, ENNReal.coe_pow]
    norm_num
  have hcoecoe : C = (196520 : ENNReal) * (K : ENNReal) * r := by
    dsimp [C, r]
    have hz : (8 * b₀ ^ 2 : ℝ≥0) ≠ 0 := by positivity
    calc
      ((196520 * K * (8 * b₀ ^ 2)⁻¹ : ℝ≥0) : ENNReal)
          = (196520 : ENNReal) * (K : ENNReal) *
              ((8 * b₀ ^ 2 : ℝ≥0) : ENNReal)⁻¹ := by
              rw [ENNReal.coe_mul, ENNReal.coe_mul, ENNReal.coe_inv hz]
              norm_num
      _ = (196520 : ENNReal) * (K : ENNReal) *
              (8 * (b₀ : ENNReal) ^ 2)⁻¹ := by rw [hcoepush]
  -- C * X * ((b₀ : ENNReal) ^ 2 * 8) = (196520 : ENNReal) * (K : ENNReal) * X
  have hem : C * X * ((b₀ : ENNReal) ^ 2 * 8) = (196520 : ENNReal) * (K : ENNReal) * X := by
    rw [hcoecoe]
    calc
      (196520 : ENNReal) * (K : ENNReal) * r * X * ((b₀ : ENNReal) ^ 2 * 8)
          = (196520 : ENNReal) * (K : ENNReal) * X *
              (r * ((b₀ : ENNReal) ^ 2 * 8)) := by ring
      _ = (196520 : ENNReal) * (K : ENNReal) * X := by rw [hrinv]; ring
  apply (ENNReal.mul_le_mul_iff_right hc0 hctop).mp
  calc
    c * μ = μ * ((b₀ : ENNReal) ^ 2 * 8) := by dsimp [c]; ring
    _ ≤ (196520 : ENNReal) * (K : ENNReal) * X := h
    _ = C * X * ((b₀ : ENNReal) ^ 2 * 8) := hem.symm
    _ = c * (C * X) := by dsimp [c]; ring

/-- **The large-`b` outer plank bound at an arbitrary maximal density, multiplied form.**

`ShadedPlank.multiplicity_le_of_isKatzTao_of_large` with the Katz--Tao input left abstract: the
density bound is an arbitrary `Δ` instead of `a ^ (-η)`.  The `a × b × 1` planks are widened to
`a × 1 × 1` slabs, which costs the factor `b` in the maximal density and in the fullness, and
Lemma 6.9 (`ShadedSlab.multiplicity_mul_le_of_maxDensity`) is applied to the widening; the two
factors of `b` are then weakened to `b₀`. -/
theorem multiplicity_mul_le_of_maxDensity_of_large {ε η : ℝ} {K b₀ : ℝ≥0} (hb₀ : 0 < b₀)
    (hK : ∀ δ' : ℝ≥0, 0 < δ' → δ' ≤ 1 →
      ((ShadedSlab.numAngleWindows δ' : ℕ) : ENNReal) ≤ (K : ENNReal) * (δ' : ENNReal) ^ (-ε))
    {κ' : Type*} (ts : Finset κ') {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (W : κ' → ShadedPlank a b hab hb1) (ha0 : 0 < a) (hbb₀ : b₀ ≤ b) (hts : ts.Nonempty)
    (hη : 0 ≤ η) {Δ : ENNReal}
    (hKT : maxDensity ts (fun j => (W j).toConvexSpaceBody) ≤ Δ)
    (hfull : (a : ℝ≥0) ^ η ≤ ShadedBody.fullness ts (fun j => (W j).toShadedBody)) :
    ShadedBody.multiplicity ts (fun j => (W j).toShadedBody)
        * (8 * (b₀ : ENNReal) ^ 2 * (a : ENNReal) ^ η) ≤
      (196520 : ENNReal) * (K : ENNReal) * (a : ENNReal) ^ (-ε) * Δ := by
  have ha1 : a ≤ 1 := hab.trans hb1
  have hb0 : 0 < b := lt_of_lt_of_le hb₀ hbb₀
  set μ : ENNReal := ShadedBody.multiplicity ts (fun j => (W j).toShadedBody) with hμ
  let lam : ℝ≥0 := b * a ^ η
  let nw : ENNReal := ((ShadedSlab.numAngleWindows a : ℕ) : ENNReal)
  have hae0 : (a : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr ha0.ne'
  have haetop : (a : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hbe0 : (b : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hb0.ne'
  have hbetop : (b : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  -- fullness of the widened family is at least `b * a ^ η`
  have hlamE : (lam : ENNReal) = (b : ENNReal) * (a : ENNReal) ^ η := by
    change ((b * a ^ η : ℝ≥0) : ENNReal) = (b : ENNReal) * (a : ENNReal) ^ η
    rw [ENNReal.coe_mul]
    rw [ENNReal.coe_rpow_of_ne_zero ha0.ne']
  have hfull_e : (a : ENNReal) ^ η ≤
      (ShadedBody.fullness ts (fun j => (W j).toShadedBody) : ENNReal) := by
    rw [← ENNReal.coe_rpow_of_ne_zero ha0.ne']
    exact_mod_cast hfull
  have hlam_EN : (lam : ENNReal) ≤
      (ShadedBody.fullness ts (fun j => ((W j).toShadedSlab ha1).toShadedBody) : ENNReal) := by
    calc
      (lam : ENNReal) = (b : ENNReal) * (a : ENNReal) ^ η := hlamE
      _ ≤ (b : ENNReal) * (ShadedBody.fullness ts (fun j => (W j).toShadedBody) : ENNReal) := by
          exact mul_le_mul_right hfull_e (b : ENNReal)
      _ ≤ (ShadedBody.fullness ts (fun j => ((W j).toShadedSlab ha1).toShadedBody) : ENNReal) := by
          exact_mod_cast (fullness_toShadedSlab_ge ha1 ha0 hb0 ts W)
  have hlam : lam ≤ ShadedBody.fullness ts (fun j => ((W j).toShadedSlab ha1).toShadedBody) :=
    ENNReal.coe_le_coe.mp hlam_EN
  -- the maximal density of the widened family is at most `Δ / b`
  have hΔ : maxDensity ts (fun j => ((W j).toShadedSlab ha1).toConvexSpaceBody) ≤
      Δ / (b : ENNReal) := by
    exact maxDensity_toShadedSlab_le ha1 hb0 ts W hKT
  -- GWZ Lemma 6.9 on the widened family
  have h69raw := ShadedSlab.multiplicity_mul_le_of_maxDensity ts (fun j => (W j).toShadedSlab ha1)
    ha0 ha1 hts (hΔ := hΔ) (lam := lam) hlam
  have h69 : μ * (8 * (lam : ENNReal)) ≤
      (196520 : ENNReal) * nw * (Δ / (b : ENNReal)) := by
    rw [hμ]
    rw [← ShadedPlank.multiplicity_toShadedSlab ha1 ts W]
    dsimp [nw]
    exact h69raw
  -- multiply by `b` and clear the division
  have hb_mul : (b : ENNReal) * (μ * (8 * (((b : ENNReal) * (a : ENNReal) ^ η)))) ≤
      (b : ENNReal) * ((196520 : ENNReal) * nw * (Δ / (b : ENNReal))) := by
    rw [hlamE] at h69
    exact mul_le_mul_right h69 (b : ENNReal)
  have hLb : (b : ENNReal) * (μ * (8 * (((b : ENNReal) * (a : ENNReal) ^ η)))) =
      μ * (8 * (b : ENNReal) ^ 2 * (a : ENNReal) ^ η) := by ring
  have hRb : (b : ENNReal) * ((196520 : ENNReal) * nw * (Δ / (b : ENNReal))) =
      (196520 : ENNReal) * nw * Δ := by
    calc
      (b : ENNReal) * ((196520 : ENNReal) * nw * (Δ / (b : ENNReal)))
          = (196520 : ENNReal) * nw * (b * (Δ / (b : ENNReal))) := by ring
      _ = (196520 : ENNReal) * nw * Δ := by
          rw [ENNReal.mul_div_cancel hbe0 hbetop]
  have hmain : μ * (8 * (b : ENNReal) ^ 2 * (a : ENNReal) ^ η) ≤
      (196520 : ENNReal) * nw * Δ := by
    rw [hLb, hRb] at hb_mul
    exact hb_mul
  -- bound the logarithmic window count
  have hKwin : nw ≤ (K : ENNReal) * (a : ENNReal) ^ (-ε) := by
    dsimp [nw]
    exact hK a ha0 ha1
  -- weaken `b ^ 2` to `b₀ ^ 2`, then chain with the window-count bound
  calc
    μ * (8 * (b₀ : ENNReal) ^ 2 * (a : ENNReal) ^ η)
        ≤ μ * (8 * (b : ENNReal) ^ 2 * (a : ENNReal) ^ η) := by
          gcongr
    _ ≤ (196520 : ENNReal) * nw * Δ := hmain
    _ ≤ (196520 : ENNReal) * (K : ENNReal) * (a : ENNReal) ^ (-ε) * Δ := by
          calc
            (196520 : ENNReal) * nw * Δ = nw * ((196520 : ENNReal) * Δ) := by ring
            _ ≤ (K : ENNReal) * (a : ENNReal) ^ (-ε) * ((196520 : ENNReal) * Δ) := by
                exact mul_le_mul_left hKwin ((196520 : ENNReal) * Δ)
            _ = (196520 : ENNReal) * (K : ENNReal) * (a : ENNReal) ^ (-ε) * Δ := by ring

/-- **The large-`b` plank bound with fullness measured at an auxiliary scale, multiplied
form.**

This is the auxiliary-scale companion of
`ShadedPlank.multiplicity_mul_le_of_maxDensity_of_large`.  The geometric plank width remains
`a`, and hence the angular-window loss remains `a ^ (-ε)`, but the fullness supplied to Lemma
6.9 may be measured at any positive `τ ≤ a`.  The proof is identical after replacing the
widened-family fullness parameter `b * a ^ η` by `b * τ ^ η`. -/
theorem multiplicity_mul_le_of_maxDensity_of_large_auxScale
    {ε η : ℝ} {K b₀ : ℝ≥0} (hb₀ : 0 < b₀)
    (hK : ∀ δ' : ℝ≥0, 0 < δ' → δ' ≤ 1 →
      ((ShadedSlab.numAngleWindows δ' : ℕ) : ENNReal) ≤
        (K : ENNReal) * (δ' : ENNReal) ^ (-ε))
    {κ' : Type*} (ts : Finset κ') {τ a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (W : κ' → ShadedPlank a b hab hb1) (hτ0 : 0 < τ) (hτa : τ ≤ a)
    (hbb₀ : b₀ ≤ b) (hts : ts.Nonempty) (hη : 0 ≤ η) {Δ : ENNReal}
    (hKT : maxDensity ts (fun j => (W j).toConvexSpaceBody) ≤ Δ)
    (hfull : τ ^ η ≤ ShadedBody.fullness ts (fun j => (W j).toShadedBody)) :
    ShadedBody.multiplicity ts (fun j => (W j).toShadedBody)
        * (8 * (b₀ : ENNReal) ^ 2 * (τ : ENNReal) ^ η) ≤
      (196520 : ENNReal) * (K : ENNReal) * (a : ENNReal) ^ (-ε) * Δ := by
  have ha0 : 0 < a := hτ0.trans_le hτa
  have ha1 : a ≤ 1 := hab.trans hb1
  have hb0 : 0 < b := lt_of_lt_of_le hb₀ hbb₀
  set μ : ENNReal := ShadedBody.multiplicity ts (fun j => (W j).toShadedBody) with hμ
  let lam : ℝ≥0 := b * τ ^ η
  let nw : ENNReal := ((ShadedSlab.numAngleWindows a : ℕ) : ENNReal)
  have hbe0 : (b : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hb0.ne'
  have hbetop : (b : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hlamE : (lam : ENNReal) = (b : ENNReal) * (τ : ENNReal) ^ η := by
    change ((b * τ ^ η : ℝ≥0) : ENNReal) = (b : ENNReal) * (τ : ENNReal) ^ η
    rw [ENNReal.coe_mul, ENNReal.coe_rpow_of_ne_zero hτ0.ne']
  have hfull_e : (τ : ENNReal) ^ η ≤
      (ShadedBody.fullness ts (fun j => (W j).toShadedBody) : ENNReal) := by
    rw [← ENNReal.coe_rpow_of_ne_zero hτ0.ne']
    exact_mod_cast hfull
  have hlam_EN : (lam : ENNReal) ≤
      (ShadedBody.fullness ts
        (fun j => ((W j).toShadedSlab ha1).toShadedBody) : ENNReal) := by
    calc
      (lam : ENNReal) = (b : ENNReal) * (τ : ENNReal) ^ η := hlamE
      _ ≤ (b : ENNReal) *
          (ShadedBody.fullness ts (fun j => (W j).toShadedBody) : ENNReal) := by
            exact mul_le_mul_right hfull_e (b : ENNReal)
      _ ≤ (ShadedBody.fullness ts
          (fun j => ((W j).toShadedSlab ha1).toShadedBody) : ENNReal) := by
            exact_mod_cast (fullness_toShadedSlab_ge ha1 ha0 hb0 ts W)
  have hlam : lam ≤
      ShadedBody.fullness ts (fun j => ((W j).toShadedSlab ha1).toShadedBody) :=
    ENNReal.coe_le_coe.mp hlam_EN
  have hΔ : maxDensity ts (fun j => ((W j).toShadedSlab ha1).toConvexSpaceBody) ≤
      Δ / (b : ENNReal) := maxDensity_toShadedSlab_le ha1 hb0 ts W hKT
  have h69raw := ShadedSlab.multiplicity_mul_le_of_maxDensity ts
    (fun j => (W j).toShadedSlab ha1) ha0 ha1 hts (hΔ := hΔ) (lam := lam) hlam
  have h69 : μ * (8 * (lam : ENNReal)) ≤
      (196520 : ENNReal) * nw * (Δ / (b : ENNReal)) := by
    rw [hμ, ← ShadedPlank.multiplicity_toShadedSlab ha1 ts W]
    dsimp [nw]
    exact h69raw
  have hb_mul : (b : ENNReal) *
      (μ * (8 * (((b : ENNReal) * (τ : ENNReal) ^ η)))) ≤
      (b : ENNReal) * ((196520 : ENNReal) * nw * (Δ / (b : ENNReal))) := by
    rw [hlamE] at h69
    exact mul_le_mul_right h69 (b : ENNReal)
  have hLb : (b : ENNReal) *
      (μ * (8 * (((b : ENNReal) * (τ : ENNReal) ^ η)))) =
      μ * (8 * (b : ENNReal) ^ 2 * (τ : ENNReal) ^ η) := by ring
  have hRb : (b : ENNReal) *
      ((196520 : ENNReal) * nw * (Δ / (b : ENNReal))) =
      (196520 : ENNReal) * nw * Δ := by
    calc
      (b : ENNReal) * ((196520 : ENNReal) * nw * (Δ / (b : ENNReal))) =
          (196520 : ENNReal) * nw * (b * (Δ / (b : ENNReal))) := by ring
      _ = (196520 : ENNReal) * nw * Δ := by
        rw [ENNReal.mul_div_cancel hbe0 hbetop]
  have hmain : μ * (8 * (b : ENNReal) ^ 2 * (τ : ENNReal) ^ η) ≤
      (196520 : ENNReal) * nw * Δ := by
    rw [hLb, hRb] at hb_mul
    exact hb_mul
  have hKwin : nw ≤ (K : ENNReal) * (a : ENNReal) ^ (-ε) := by
    dsimp [nw]
    exact hK a ha0 ha1
  calc
    μ * (8 * (b₀ : ENNReal) ^ 2 * (τ : ENNReal) ^ η) ≤
        μ * (8 * (b : ENNReal) ^ 2 * (τ : ENNReal) ^ η) := by gcongr
    _ ≤ (196520 : ENNReal) * nw * Δ := hmain
    _ ≤ (196520 : ENNReal) * (K : ENNReal) * (a : ENNReal) ^ (-ε) * Δ := by
      calc
        (196520 : ENNReal) * nw * Δ = nw * ((196520 : ENNReal) * Δ) := by ring
        _ ≤ (K : ENNReal) * (a : ENNReal) ^ (-ε) *
            ((196520 : ENNReal) * Δ) := by
          exact mul_le_mul_left hKwin ((196520 : ENNReal) * Δ)
        _ = (196520 : ENNReal) * (K : ENNReal) * (a : ENNReal) ^ (-ε) * Δ := by ring

/-- **The large-`b` plank bound with fullness and loss paid at an auxiliary scale.**

After clearing the positive fullness factor in
`ShadedPlank.multiplicity_mul_le_of_maxDensity_of_large_auxScale`, the geometric angular loss
`a ^ (-ε)` is weakened to `τ ^ (-ε)` using `τ ≤ a`. -/
theorem multiplicity_le_of_maxDensity_of_large_auxScale
    {ε η : ℝ} {K b₀ : ℝ≥0} (hb₀ : 0 < b₀) (hε : 0 ≤ ε)
    (hK : ∀ δ' : ℝ≥0, 0 < δ' → δ' ≤ 1 →
      ((ShadedSlab.numAngleWindows δ' : ℕ) : ENNReal) ≤
        (K : ENNReal) * (δ' : ENNReal) ^ (-ε))
    {κ' : Type*} (ts : Finset κ') {τ a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (W : κ' → ShadedPlank a b hab hb1) (hτ0 : 0 < τ) (hτa : τ ≤ a)
    (hbb₀ : b₀ ≤ b) (hts : ts.Nonempty) (hη : 0 ≤ η) {Δ : ENNReal}
    (hKT : maxDensity ts (fun j => (W j).toConvexSpaceBody) ≤ Δ)
    (hfull : τ ^ η ≤ ShadedBody.fullness ts (fun j => (W j).toShadedBody)) :
    ShadedBody.multiplicity ts (fun j => (W j).toShadedBody) ≤
      ((196520 * K * (8 * b₀ ^ 2)⁻¹ : ℝ≥0) : ENNReal) *
        (τ : ENNReal) ^ (-(ε + η)) * Δ := by
  let μ : ENNReal := ShadedBody.multiplicity ts (fun j => (W j).toShadedBody)
  let X : ENNReal := (τ : ENNReal) ^ (-(ε + η))
  let c : ENNReal := 8 * (b₀ : ENNReal) ^ 2 * (τ : ENNReal) ^ η
  let r : ENNReal := (8 * (b₀ : ENNReal) ^ 2)⁻¹
  let C : ENNReal := ((196520 * K * (8 * b₀ ^ 2)⁻¹ : ℝ≥0) : ENNReal)
  have h := multiplicity_mul_le_of_maxDensity_of_large_auxScale hb₀ hK ts W hτ0 hτa
    hbb₀ hts hη hKT hfull
  have ha0 : 0 < a := hτ0.trans_le hτa
  have hloss : (a : ENNReal) ^ (-ε) ≤ (τ : ENNReal) ^ (-ε) := by
    have hNN : a ^ (-ε) ≤ τ ^ (-ε) :=
      NNReal.rpow_le_rpow_of_nonpos hτ0 hτa (neg_nonpos.mpr hε)
    rw [← ENNReal.coe_rpow_of_ne_zero ha0.ne',
      ← ENNReal.coe_rpow_of_ne_zero hτ0.ne']
    exact_mod_cast hNN
  have h' : μ * (8 * (b₀ : ENNReal) ^ 2 * (τ : ENNReal) ^ η) ≤
      (196520 : ENNReal) * (K : ENNReal) * (τ : ENNReal) ^ (-ε) * Δ :=
    h.trans (by gcongr)
  have hτe0 : (τ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hτ0.ne'
  have hτetop : (τ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hb2ne0 : 8 * (b₀ : ENNReal) ^ 2 ≠ 0 := by positivity
  have hb2top : 8 * (b₀ : ENNReal) ^ 2 ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by norm_num : (8 : ENNReal) ≠ ⊤)
      (ENNReal.pow_ne_top ENNReal.coe_ne_top)
  have hpow0 : (τ : ENNReal) ^ η ≠ 0 := by simp [hτe0, hτetop]
  have hpowtop : (τ : ENNReal) ^ η ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_ne_zero hτe0 hτetop
  have hc0 : c ≠ 0 := by
    dsimp [c]
    exact mul_ne_zero hb2ne0 hpow0
  have hctop : c ≠ ⊤ := by
    dsimp [c]
    exact ENNReal.mul_ne_top hb2top hpowtop
  have hrinv : r * (8 * (b₀ : ENNReal) ^ 2) = 1 := by
    dsimp [r]
    exact ENNReal.inv_mul_cancel hb2ne0 hb2top
  have hcoepush : ((8 * b₀ ^ 2 : ℝ≥0) : ENNReal) = 8 * (b₀ : ENNReal) ^ 2 := by
    rw [ENNReal.coe_mul, ENNReal.coe_pow]
    norm_num
  have hcoecoe : C = (196520 : ENNReal) * (K : ENNReal) * r := by
    dsimp [C, r]
    have hz : (8 * b₀ ^ 2 : ℝ≥0) ≠ 0 := by positivity
    calc
      ((196520 * K * (8 * b₀ ^ 2)⁻¹ : ℝ≥0) : ENNReal) =
          (196520 : ENNReal) * (K : ENNReal) *
            ((8 * b₀ ^ 2 : ℝ≥0) : ENNReal)⁻¹ := by
              rw [ENNReal.coe_mul, ENNReal.coe_mul, ENNReal.coe_inv hz]
              norm_num
      _ = (196520 : ENNReal) * (K : ENNReal) *
          (8 * (b₀ : ENNReal) ^ 2)⁻¹ := by rw [hcoepush]
  have hCmul : C * (8 * (b₀ : ENNReal) ^ 2) =
      (196520 : ENNReal) * (K : ENNReal) := by
    rw [hcoecoe]
    calc
      (196520 : ENNReal) * (K : ENNReal) * r * (8 * (b₀ : ENNReal) ^ 2) =
          (196520 : ENNReal) * (K : ENNReal) *
            (r * (8 * (b₀ : ENNReal) ^ 2)) := by ring
      _ = (196520 : ENNReal) * (K : ENNReal) := by rw [hrinv]; ring
  have hprod : (τ : ENNReal) ^ (-(ε + η)) * (τ : ENNReal) ^ η =
      (τ : ENNReal) ^ (-ε) := by
    rw [← ENNReal.rpow_add (-(ε + η)) η hτe0 hτetop]
    congr 1
    ring
  apply (ENNReal.mul_le_mul_iff_right hc0 hctop).mp
  calc
    c * μ = μ * (8 * (b₀ : ENNReal) ^ 2 * (τ : ENNReal) ^ η) := by
      dsimp [c]
      ring
    _ ≤ (196520 : ENNReal) * (K : ENNReal) * (τ : ENNReal) ^ (-ε) * Δ := h'
    _ = c * (C * X * Δ) := by
      calc
        (196520 : ENNReal) * (K : ENNReal) * (τ : ENNReal) ^ (-ε) * Δ =
            C * (8 * (b₀ : ENNReal) ^ 2) *
              ((τ : ENNReal) ^ (-(ε + η)) * (τ : ENNReal) ^ η) * Δ := by
                rw [← hCmul, ← hprod]
        _ = (C * X * Δ) *
            (8 * (b₀ : ENNReal) ^ 2 * (τ : ENNReal) ^ η) := by
              dsimp [X]
              ring
        _ = c * (C * X * Δ) := by
          dsimp [c]
          ring

/-- **The large-`b` outer plank bound at an arbitrary maximal density.**

`ShadedPlank.multiplicity_le_of_isKatzTao_of_large'` with the Katz--Tao input left abstract: the
density bound is an arbitrary `Δ` instead of `a ^ (-η)`, and only the fullness keeps the shape
`a ^ η`.  The proof is the same widening — `Δ_max` of the `a × 1 × 1` slab family is at most `Δ / b`
and its fullness at least `b · a ^ η`, so Lemma 6.9 gives
`μ · 8 b² a ^ η ≤ 196520 · (window count) · Δ` — and the two factors `b² ≥ b₀²`, `a ^ η` are cleared
at the end.

Part (A) of GWZ Proposition 6.6 needs this form: there the outer planks arise parentwise, so the
available density bound is the pooled `|parents| · C_KT` of
`Kakeya.maxDensity_le_sum_of_parentwise`, which is sub-polynomial in `δ` but *not* of the form
`a ^ (-η)`. -/
theorem multiplicity_le_of_maxDensity_of_large {ε η : ℝ} {K b₀ : ℝ≥0} (hb₀ : 0 < b₀)
    (hK : ∀ δ' : ℝ≥0, 0 < δ' → δ' ≤ 1 →
      ((ShadedSlab.numAngleWindows δ' : ℕ) : ENNReal) ≤ (K : ENNReal) * (δ' : ENNReal) ^ (-ε))
    {κ' : Type*} (ts : Finset κ') {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (W : κ' → ShadedPlank a b hab hb1) (ha0 : 0 < a) (hbb₀ : b₀ ≤ b) (hts : ts.Nonempty)
    (hη : 0 ≤ η) {Δ : ENNReal}
    (hKT : maxDensity ts (fun j => (W j).toConvexSpaceBody) ≤ Δ)
    (hfull : (a : ℝ≥0) ^ η ≤ ShadedBody.fullness ts (fun j => (W j).toShadedBody)) :
    ShadedBody.multiplicity ts (fun j => (W j).toShadedBody) ≤
      ((196520 * K * (8 * b₀ ^ 2)⁻¹ : ℝ≥0) : ENNReal) * (a : ENNReal) ^ (-(ε + η)) * Δ := by
  let μ : ENNReal := ShadedBody.multiplicity ts (fun j => (W j).toShadedBody)
  let X : ENNReal := (a : ENNReal) ^ (-(ε + η))
  let c : ENNReal := 8 * (b₀ : ENNReal) ^ 2 * (a : ENNReal) ^ η
  let r : ENNReal := (8 * (b₀ : ENNReal) ^ 2)⁻¹
  let C : ENNReal := ((196520 * K * (8 * b₀ ^ 2)⁻¹ : ℝ≥0) : ENNReal)
  have h := multiplicity_mul_le_of_maxDensity_of_large hb₀ hK ts W ha0 hbb₀ hts hη hKT hfull
  -- h : μ * (8 * (b₀ : ENNReal) ^ 2 * (a : ENNReal) ^ η) ≤
  --     (196520 : ENNReal) * (K : ENNReal) * (a : ENNReal) ^ (-ε) * Δ
  have hae0 : (a : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr ha0.ne'
  have haetop : (a : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hb2ne0 : 8 * (b₀ : ENNReal) ^ 2 ≠ 0 := by positivity
  have hb2top : 8 * (b₀ : ENNReal) ^ 2 ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by norm_num : (8 : ENNReal) ≠ ⊤)
      (ENNReal.pow_ne_top (by exact ENNReal.coe_ne_top : (b₀ : ENNReal) ≠ ⊤))
  have hane0 : (a : ENNReal) ^ η ≠ 0 := by
    simp [hae0, haetop]
  have hanet : (a : ENNReal) ^ η ≠ ⊤ := ENNReal.rpow_ne_top_of_ne_zero hae0 haetop
  have hc0 : c ≠ 0 := by
    dsimp [c]
    exact mul_ne_zero hb2ne0 hane0
  have hctop : c ≠ ⊤ := by
    dsimp [c]
    exact ENNReal.mul_ne_top hb2top hanet
  have hrinv : r * (8 * (b₀ : ENNReal) ^ 2) = 1 := by
    dsimp [r]
    exact ENNReal.inv_mul_cancel hb2ne0 hb2top
  have hcoepush : ((8 * b₀ ^ 2 : ℝ≥0) : ENNReal) = 8 * (b₀ : ENNReal) ^ 2 := by
    rw [ENNReal.coe_mul, ENNReal.coe_pow]
    norm_num
  have hcoecoe : C = (196520 : ENNReal) * (K : ENNReal) * r := by
    dsimp [C, r]
    have hz : (8 * b₀ ^ 2 : ℝ≥0) ≠ 0 := by positivity
    calc
      ((196520 * K * (8 * b₀ ^ 2)⁻¹ : ℝ≥0) : ENNReal)
          = (196520 : ENNReal) * (K : ENNReal) *
              ((8 * b₀ ^ 2 : ℝ≥0) : ENNReal)⁻¹ := by
              rw [ENNReal.coe_mul, ENNReal.coe_mul, ENNReal.coe_inv hz]
              norm_num
      _ = (196520 : ENNReal) * (K : ENNReal) *
              (8 * (b₀ : ENNReal) ^ 2)⁻¹ := by rw [hcoepush]
  have hCmul : C * (8 * (b₀ : ENNReal) ^ 2) = (196520 : ENNReal) * (K : ENNReal) := by
    rw [hcoecoe]
    calc
      (196520 : ENNReal) * (K : ENNReal) * r * (8 * (b₀ : ENNReal) ^ 2)
          = (196520 : ENNReal) * (K : ENNReal) * (r * (8 * (b₀ : ENNReal) ^ 2)) := by ring
      _ = (196520 : ENNReal) * (K : ENNReal) := by rw [hrinv]; ring
  have hprod : (a : ENNReal) ^ (-(ε + η)) * (a : ENNReal) ^ η = (a : ENNReal) ^ (-ε) := by
    rw [← ENNReal.rpow_add (-(ε + η)) η hae0 haetop]
    congr 1
    ring
  apply (ENNReal.mul_le_mul_iff_right hc0 hctop).mp
  calc
    c * μ = μ * (8 * (b₀ : ENNReal) ^ 2 * (a : ENNReal) ^ η) := by dsimp [c]; ring
    _ ≤ (196520 : ENNReal) * (K : ENNReal) * (a : ENNReal) ^ (-ε) * Δ := h
    _ = c * (C * X * Δ) := by
      calc
        (196520 : ENNReal) * (K : ENNReal) * (a : ENNReal) ^ (-ε) * Δ
            = C * (8 * (b₀ : ENNReal) ^ 2) *
                ((a : ENNReal) ^ (-(ε + η)) * (a : ENNReal) ^ η) * Δ := by
                rw [← hCmul, ← hprod]
        _ = (C * X * Δ) * (8 * (b₀ : ENNReal) ^ 2 * (a : ENNReal) ^ η) := by
                dsimp [X]; ring
        _ = c * (C * X * Δ) := by dsimp [c]; ring

end ShadedPlank

namespace Kakeya

/-! ### Pooling a parentwise Katz--Tao bound into a global one

GWZ Lemma 6.9 needs `Δ_max` of the family it is applied to.  In part (B) that bound is global and is
supplied directly by the factorisation datum.  In part (A) the outer planks arise *parentwise* and
are then pooled, and only a parentwise bound is available; the theorem below is the exact cost of
pooling.  Note that the factor is the number of parents that can contribute to *one test body*, not
the total: `Kakeya.ExternalParentSystem.boundedOverlapThroughLeaves` bounds precisely such a count,
but only for *tube*-shaped test bodies of radius `8ρ`, whereas Lemma 6.9 tests against *slab*-shaped
bodies.  See the docstring of `Kakeya.coarseSlabFallback` for what is still missing.
-/

/-- **Parentwise Katz--Tao bounds pool into a global one, at the cost of the number of parents.**

If every index of `s` has its parent in `P` and each parent fibre has maximal density at most `Δ`,
then `Δ_max(s) ≤ |P| · Δ`.  The proof is the exact fibrewise splitting of the density numerator, so
the factor `|P|` can be replaced by the number of parents contributing to the *particular* test body
whenever such a count is available. -/
theorem maxDensity_le_sum_of_parentwise {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    {s : Finset ι} {V : ι → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    {par : ι → κ} {P : Finset κ} (hpar : ∀ i ∈ s, par i ∈ P)
    {Δ : ENNReal} (hΔ : ∀ k ∈ P, maxDensity {i ∈ s | par i = k} V ≤ Δ) :
    maxDensity s V ≤ (P.card : ENNReal) * Δ := by
  rw [maxDensity_le_iff]
  intro K
  rw [densityIn_le_iff]
  calc
    (∑ i ∈ s with V i ≤ K, volume (V i).carrier)
        = ∑ k ∈ P, ∑ i ∈ (s.filter (fun i => V i ≤ K)).filter (fun i => par i = k),
            volume (V i).carrier := by
          symm
          refine Finset.sum_fiberwise_of_maps_to (s := s.filter (fun i => V i ≤ K))
            (t := P) (g := par) (f := fun i => volume (V i).carrier) ?_
          intro i hi
          exact hpar i (Finset.mem_filter.mp hi).1
    _ ≤ ∑ k ∈ P, Δ * volume K.carrier := by
          refine Finset.sum_le_sum ?_
          intro k hk
          rw [Finset.filter_comm]
          have hden : densityIn ({i ∈ s | par i = k}) V K ≤ Δ :=
            (le_maxDensity (s := {i ∈ s | par i = k}) (W := V) K).trans (hΔ k hk)
          exact (densityIn_le_iff ({i ∈ s | par i = k}) V K Δ).mp hden
    _ = (P.card : ENNReal) * (Δ * volume K.carrier) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ = (P.card : ENNReal) * Δ * volume K.carrier := by rw [mul_assoc]

/-! ### What the two Section-6 fallback branches need on top of Lemma 6.9

The large-`b` branches of GWZ Proposition 6.6(A) and 6.6(B) consume Lemma 6.9 only through the two
`ENNReal` inequalities below.  Both are pure algebra; the content is *which* scale facts make the
proposition's target weaker than a sub-polynomial multiplicity bound.
-/

/-- The three-atom collapse behind `Kakeya.combineLocalFactorFallbackNN`: the outer 6.4-shaped factor
of `Kakeya.combineLocalFactor_rpow`, multiplied by the leftover `b ^ (5β/2-1)` and the inverse Frostman
mass, is exactly `1`.  Equivalently
`(b/a) ^ (β/2) · (a/b) · b ^ (-2β) · (b ^ 2 |ts|) ^ (1-β/2) = (a |ts|) ^ (1-β/2) · b ^ (1-5β/2)`. -/
theorem massFactor_rpow_collect {β : ℝ} {a b : ℝ≥0} {nts : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hnts : nts ≠ 0) :
    (b / a) ^ (β / 2) * (a / b) * b ^ (-2 * β) * (b ^ 2 * (nts : ℝ≥0)) ^ (1 - β / 2)
        * b ^ (5 * β / 2 - 1) * ((a * (nts : ℝ≥0)) ^ (1 - β / 2))⁻¹ = 1 := by
  have hnts' : (nts : ℝ≥0) ≠ 0 := by exact_mod_cast hnts
  -- expand the compound powers into pure rpows of the atoms `a`, `b`, `(nts : ℝ≥0)`
  have h1 : (b / a) ^ (β / 2) = b ^ (β / 2) * a ^ (-(β / 2)) := by
    rw [NNReal.div_rpow]
    rw [div_eq_mul_inv]
    rw [← NNReal.rpow_neg a (β / 2)]
  have h2 : a / b = a * b ^ (-1 : ℝ) := by
    rw [div_eq_mul_inv]
    congr 1
    rw [NNReal.rpow_neg b (1 : ℝ)]
    simp
  have h3 : (b ^ 2 * (nts : ℝ≥0)) ^ (1 - β / 2) =
      b ^ ((2 : ℝ) * (1 - β / 2)) * (nts : ℝ≥0) ^ (1 - β / 2) := by
    rw [NNReal.mul_rpow]
    congr 1
    calc
      (b ^ (2 : ℕ)) ^ (1 - β / 2) = (b ^ (2 : ℝ)) ^ (1 - β / 2) := by
        exact congrArg (fun x : ℝ≥0 => x ^ (1 - β / 2)) (NNReal.rpow_natCast b 2).symm
      _ = b ^ ((2 : ℝ) * (1 - β / 2)) := by
        exact (NNReal.rpow_mul b (2 : ℝ) (1 - β / 2)).symm
  have h4 : ((a * (nts : ℝ≥0)) ^ (1 - β / 2))⁻¹ = (a * (nts : ℝ≥0)) ^ (-(1 - β / 2)) := by
    rw [← NNReal.rpow_neg (a * (nts : ℝ≥0)) (1 - β / 2)]
  have h5 : (a * (nts : ℝ≥0)) ^ (-(1 - β / 2)) =
      a ^ (-(1 - β / 2)) * (nts : ℝ≥0) ^ (-(1 - β / 2)) := by
    rw [NNReal.mul_rpow]
  -- the exponent of each atom sums to `0`, so each atom's contribution collapses to `1`
  have hcolA : a ^ (-(β / 2)) * a * a ^ (-(1 - β / 2)) = 1 := by
    calc
      a ^ (-(β / 2)) * a * a ^ (-(1 - β / 2))
          = a ^ (-(β / 2)) * a ^ (1 : ℝ) * a ^ (-(1 - β / 2)) := by
            nth_rw 2 [← NNReal.rpow_one a]
      _ = a ^ (-(β / 2) + (1 : ℝ) + (-(1 - β / 2))) := by
            repeat' rw [← NNReal.rpow_add ha]
      _ = a ^ (0 : ℝ) := by congr 1; ring
      _ = (1 : ℝ≥0) := by rw [NNReal.rpow_zero]
  have hcolB : b ^ (β / 2) * b ^ (-1 : ℝ) * b ^ (-2 * β) * b ^ (2 * (1 - β / 2))
      * b ^ (5 * β / 2 - 1) = 1 := by
    calc
      b ^ (β / 2) * b ^ (-1 : ℝ) * b ^ (-2 * β) * b ^ (2 * (1 - β / 2))
          * b ^ (5 * β / 2 - 1)
          = b ^ ((β / 2) + (-1 : ℝ) + (-2 * β) + (2 * (1 - β / 2)) + (5 * β / 2 - 1)) := by
            repeat' rw [← NNReal.rpow_add hb]
      _ = b ^ (0 : ℝ) := by congr 1; ring
      _ = (1 : ℝ≥0) := by rw [NNReal.rpow_zero]
  have hcolN : (nts : ℝ≥0) ^ (1 - β / 2) * (nts : ℝ≥0) ^ (-(1 - β / 2)) = 1 := by
    calc
      (nts : ℝ≥0) ^ (1 - β / 2) * (nts : ℝ≥0) ^ (-(1 - β / 2))
          = (nts : ℝ≥0) ^ ((1 - β / 2) + (-(1 - β / 2))) := by
            rw [← NNReal.rpow_add hnts' (1 - β / 2) (-(1 - β / 2))]
      _ = (nts : ℝ≥0) ^ (0 : ℝ) := by congr 1; ring
      _ = (1 : ℝ≥0) := by rw [NNReal.rpow_zero]
  calc
    (b / a) ^ (β / 2) * (a / b) * b ^ (-2 * β) * (b ^ 2 * (nts : ℝ≥0)) ^ (1 - β / 2)
        * b ^ (5 * β / 2 - 1) * ((a * (nts : ℝ≥0)) ^ (1 - β / 2))⁻¹
    = b ^ (β / 2) * a ^ (-(β / 2)) * (a * b ^ (-1 : ℝ)) * b ^ (-2 * β)
        * (b ^ ((2 : ℝ) * (1 - β / 2)) * (nts : ℝ≥0) ^ (1 - β / 2))
        * b ^ (5 * β / 2 - 1) * ((a * (nts : ℝ≥0)) ^ (1 - β / 2))⁻¹ := by
        rw [h1, h2, h3]
    _ = b ^ (β / 2) * a ^ (-(β / 2)) * a * b ^ (-1 : ℝ) * b ^ (-2 * β)
        * b ^ ((2 : ℝ) * (1 - β / 2)) * (nts : ℝ≥0) ^ (1 - β / 2)
        * b ^ (5 * β / 2 - 1) * ((a * (nts : ℝ≥0)) ^ (1 - β / 2))⁻¹ := by
        ring
    _ = b ^ (β / 2) * a ^ (-(β / 2)) * a * b ^ (-1 : ℝ) * b ^ (-2 * β)
        * b ^ ((2 : ℝ) * (1 - β / 2)) * (nts : ℝ≥0) ^ (1 - β / 2)
        * b ^ (5 * β / 2 - 1) * ((a * (nts : ℝ≥0)) ^ (-(1 - β / 2))) := by
        rw [h4]
    _ = b ^ (β / 2) * a ^ (-(β / 2)) * a * b ^ (-1 : ℝ) * b ^ (-2 * β)
        * b ^ ((2 : ℝ) * (1 - β / 2)) * (nts : ℝ≥0) ^ (1 - β / 2)
        * b ^ (5 * β / 2 - 1)
        * (a ^ (-(1 - β / 2)) * (nts : ℝ≥0) ^ (-(1 - β / 2))) := by
        rw [h5]
    _ = (a ^ (-(β / 2)) * a * a ^ (-(1 - β / 2)))
        * (b ^ (β / 2) * b ^ (-1 : ℝ) * b ^ (-2 * β) * b ^ ((2 : ℝ) * (1 - β / 2))
            * b ^ (5 * β / 2 - 1))
        * ((nts : ℝ≥0) ^ (1 - β / 2) * (nts : ℝ≥0) ^ (-(1 - β / 2))) := by
        ring
    _ = (1 : ℝ≥0) * 1 * 1 := by
        rw [hcolA, hcolB, hcolN]
    _ = 1 := by ring

/-- **The `ℝ≥0` identity behind the Proposition 6.6(A) large-`b` combination.**

The part-(A) μ-split carries its inner factor pre-multiplied, and this identity rewrites that factor
in the shape of the part-(A) target: the two transverse powers combine into `(a/b) ^ (3β/2)`, the
`δ`-powers into `δ ^ (-2β) · (δ ^ 2 |q|) ^ (1-β/2)`, and what is left over is exactly the *inverse* of
the Frostman mass `(a · |ts|) ^ (1-β/2)` together with the harmless `b ^ (5β/2-1)`. -/
theorem combineLocalFactorFallbackNN {β ε : ℝ} {a b δ : ℝ≥0} {nq nts : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hδ : δ ≠ 0) (hnts : nts ≠ 0) (hnq : nq ≠ 0) :
    δ ^ (-(ε / 3)) * (a / b) ^ (1 - β) * (a⁻¹ * δ) ^ (-2 * β)
        * ((a ^ 2)⁻¹ * δ ^ 2 * ((nq : ℝ≥0) / (nts : ℝ≥0))) ^ (1 - β / 2)
      = δ ^ (-(ε / 3)) * δ ^ (-2 * β) * (δ ^ 2 * (nq : ℝ≥0)) ^ (1 - β / 2)
        * (a / b) ^ (3 * β / 2) * b ^ (5 * β / 2 - 1)
        * ((a * (nts : ℝ≥0)) ^ (1 - β / 2))⁻¹ := by
  -- `(a/b)^(1-β)` splits into `a^(1-β) * b^(-(1-β))`
  have h_ab : (a / b) ^ (1 - β) = a ^ (1 - β) * b ^ (-(1 - β)) := by
    rw [NNReal.div_rpow, div_eq_mul_inv]
    rw [← NNReal.rpow_neg b (1 - β)]
  -- `(a/b)^(3β/2)` splits into `a^(3β/2) * b^(-(3β/2))`
  have h_ab2 : (a / b) ^ (3 * β / 2) = a ^ (3 * β / 2) * b ^ (-(3 * β / 2)) := by
    rw [NNReal.div_rpow, div_eq_mul_inv]
    rw [← NNReal.rpow_neg b (3 * β / 2)]
  -- `(a⁻¹)^(-2β) = a^(2β)`
  have h_inv_pow : (a⁻¹) ^ (-2 * β) = a ^ (2 * β) := by
    calc
      (a⁻¹) ^ (-2 * β) = (a ^ (-2 * β))⁻¹ := by rw [NNReal.inv_rpow]
      _ = (a ^ (-(2 * β)))⁻¹ := by ring_nf
      _ = ((a ^ (2 * β))⁻¹)⁻¹ := by rw [NNReal.rpow_neg a (2 * β)]
      _ = a ^ (2 * β) := by simp
  -- `(a⁻¹·δ)^(-2β) = a^(2β)·δ^(-2β)`
  have h2 : (a⁻¹ * δ) ^ (-2 * β) = a ^ (2 * β) * δ ^ (-2 * β) := by
    rw [NNReal.mul_rpow, h_inv_pow]
  -- `((a^2)⁻¹)^(1-β/2) = a^(β-2)`
  have hf1 : ((a ^ 2)⁻¹) ^ (1 - β / 2) = a ^ (β - 2) := by
    have hsq : (a ^ 2)⁻¹ = a ^ (-(2 : ℝ)) := by
      rw [show a ^ 2 = a ^ (2 : ℝ) by exact (NNReal.rpow_natCast a 2).symm]
      rw [← NNReal.rpow_neg a (2 : ℝ)]
    rw [hsq]
    calc
      (a ^ (-(2 : ℝ))) ^ (1 - β / 2) = a ^ ((-(2 : ℝ)) * (1 - β / 2)) :=
        (NNReal.rpow_mul a (-(2 : ℝ)) (1 - β / 2)).symm
      _ = a ^ (β - 2) := by congr 1; ring
  -- `(δ^2)^(1-β/2) = δ^(2-β)`
  have hf2 : (δ ^ 2) ^ (1 - β / 2) = δ ^ (2 - β) := by
    rw [show δ ^ 2 = δ ^ (2 : ℝ) by exact (NNReal.rpow_natCast δ 2).symm]
    calc
      (δ ^ (2 : ℝ)) ^ (1 - β / 2) = δ ^ ((2 : ℝ) * (1 - β / 2)) :=
        (NNReal.rpow_mul δ (2 : ℝ) (1 - β / 2)).symm
      _ = δ ^ (2 - β) := by congr 1; ring
  -- `(nts⁻¹)^(1-β/2) = nts^(-(1-β/2))`
  have hf3 : ((nts : ℝ≥0)⁻¹) ^ (1 - β / 2) = (nts : ℝ≥0) ^ (-(1 - β / 2)) := by
    rw [NNReal.inv_rpow]
    rw [← NNReal.rpow_neg (nts : ℝ≥0) (1 - β / 2)]
  -- split the large `(1-β/2)`-power into the four atom-powers
  have hbig : ((a ^ 2)⁻¹ * δ ^ 2 * ((nq : ℝ≥0) / (nts : ℝ≥0))) ^ (1 - β / 2)
      = a ^ (β - 2) * δ ^ (2 - β) * (nq : ℝ≥0) ^ (1 - β / 2)
        * (nts : ℝ≥0) ^ (-(1 - β / 2)) := by
    rw [div_eq_mul_inv]
    rw [show (a ^ 2)⁻¹ * δ ^ 2 * ((nq : ℝ≥0) * ((nts : ℝ≥0)⁻¹))
        = ((a ^ 2)⁻¹ * δ ^ 2 * (nq : ℝ≥0)) * ((nts : ℝ≥0)⁻¹) by ring]
    rw [NNReal.mul_rpow]
    rw [NNReal.mul_rpow]
    rw [NNReal.mul_rpow]
    rw [hf1, hf2, hf3]
  -- `(δ^2·nq)^(1-β/2) = δ^(2-β)·nq^(1-β/2)`
  have h_split_del : (δ ^ 2 * (nq : ℝ≥0)) ^ (1 - β / 2)
      = δ ^ (2 - β) * (nq : ℝ≥0) ^ (1 - β / 2) := by
    rw [NNReal.mul_rpow, hf2]
  -- `(a·nts)^(1-β/2))⁻¹ = a^(β/2-1)·nts^(-(1-β/2))`
  have h_inv_mass : ((a * (nts : ℝ≥0)) ^ (1 - β / 2))⁻¹
      = a ^ (β / 2 - 1) * (nts : ℝ≥0) ^ (-(1 - β / 2)) := by
    rw [← NNReal.rpow_neg (a * (nts : ℝ≥0)) (1 - β / 2)]
    rw [NNReal.mul_rpow]
    have ham : a ^ (-(1 - β / 2)) = a ^ (β / 2 - 1) := by congr 1; ring
    rw [ham]
  -- exponent re-bracketings
  have h_a_expo : a ^ ((1 - β) + (2 * β) + (β - 2)) = a ^ (2 * β - 1) := by congr 1; ring
  have h_b_neg : b ^ (-(1 - β)) = b ^ (β - 1) := by congr 1; ring
  have h_a_expo2 : a ^ ((3 * β / 2) + (β / 2 - 1)) = a ^ (2 * β - 1) := by congr 1; ring
  have h_b_expo2 : b ^ (-(3 * β / 2) + (5 * β / 2 - 1)) = b ^ (β - 1) := by congr 1; ring
  -- the canonical product of pure atom-powers that both sides reduce to
  have hL : δ ^ (-(ε / 3)) * (a / b) ^ (1 - β) * (a⁻¹ * δ) ^ (-2 * β)
        * ((a ^ 2)⁻¹ * δ ^ 2 * ((nq : ℝ≥0) / (nts : ℝ≥0))) ^ (1 - β / 2)
      = δ ^ (-(ε / 3)) * δ ^ (-2 * β) * δ ^ (2 - β) * (nq : ℝ≥0) ^ (1 - β / 2)
        * (nts : ℝ≥0) ^ (-(1 - β / 2)) * a ^ (2 * β - 1) * b ^ (β - 1) := by
    calc
      δ ^ (-(ε / 3)) * (a / b) ^ (1 - β) * (a⁻¹ * δ) ^ (-2 * β)
          * ((a ^ 2)⁻¹ * δ ^ 2 * ((nq : ℝ≥0) / (nts : ℝ≥0))) ^ (1 - β / 2)
      = δ ^ (-(ε / 3)) * (a ^ (1 - β) * b ^ (-(1 - β))) * (a ^ (2 * β) * δ ^ (-2 * β))
          * (a ^ (β - 2) * δ ^ (2 - β) * (nq : ℝ≥0) ^ (1 - β / 2)
            * (nts : ℝ≥0) ^ (-(1 - β / 2))) := by
          rw [h_ab, h2, hbig]
      _ = δ ^ (-(ε / 3)) * δ ^ (-2 * β) * δ ^ (2 - β) * (nq : ℝ≥0) ^ (1 - β / 2)
          * (nts : ℝ≥0) ^ (-(1 - β / 2))
          * (a ^ (1 - β) * a ^ (2 * β) * a ^ (β - 2)) * b ^ (-(1 - β)) := by
          ring
      _ = δ ^ (-(ε / 3)) * δ ^ (-2 * β) * δ ^ (2 - β) * (nq : ℝ≥0) ^ (1 - β / 2)
          * (nts : ℝ≥0) ^ (-(1 - β / 2))
          * a ^ ((1 - β) + (2 * β) + (β - 2)) * b ^ (-(1 - β)) := by
          rw [← NNReal.rpow_add ha, ← NNReal.rpow_add ha]
      _ = δ ^ (-(ε / 3)) * δ ^ (-2 * β) * δ ^ (2 - β) * (nq : ℝ≥0) ^ (1 - β / 2)
          * (nts : ℝ≥0) ^ (-(1 - β / 2)) * a ^ (2 * β - 1) * b ^ (β - 1) := by
          rw [h_a_expo, h_b_neg]
  have hR : δ ^ (-(ε / 3)) * δ ^ (-2 * β) * (δ ^ 2 * (nq : ℝ≥0)) ^ (1 - β / 2)
      * (a / b) ^ (3 * β / 2) * b ^ (5 * β / 2 - 1) * ((a * (nts : ℝ≥0)) ^ (1 - β / 2))⁻¹
      = δ ^ (-(ε / 3)) * δ ^ (-2 * β) * δ ^ (2 - β) * (nq : ℝ≥0) ^ (1 - β / 2)
        * (nts : ℝ≥0) ^ (-(1 - β / 2)) * a ^ (2 * β - 1) * b ^ (β - 1) := by
    calc
      δ ^ (-(ε / 3)) * δ ^ (-2 * β) * (δ ^ 2 * (nq : ℝ≥0)) ^ (1 - β / 2)
          * (a / b) ^ (3 * β / 2) * b ^ (5 * β / 2 - 1)
          * ((a * (nts : ℝ≥0)) ^ (1 - β / 2))⁻¹
      = δ ^ (-(ε / 3)) * δ ^ (-2 * β) * (δ ^ (2 - β) * (nq : ℝ≥0) ^ (1 - β / 2))
          * (a ^ (3 * β / 2) * b ^ (-(3 * β / 2))) * b ^ (5 * β / 2 - 1)
          * (a ^ (β / 2 - 1) * (nts : ℝ≥0) ^ (-(1 - β / 2))) := by
          rw [h_split_del, h_ab2, h_inv_mass]
      _ = δ ^ (-(ε / 3)) * δ ^ (-2 * β) * δ ^ (2 - β) * (nq : ℝ≥0) ^ (1 - β / 2)
          * (nts : ℝ≥0) ^ (-(1 - β / 2))
          * (a ^ (3 * β / 2) * a ^ (β / 2 - 1)) * (b ^ (-(3 * β / 2)) * b ^ (5 * β / 2 - 1)) := by
          ring
      _ = δ ^ (-(ε / 3)) * δ ^ (-2 * β) * δ ^ (2 - β) * (nq : ℝ≥0) ^ (1 - β / 2)
          * (nts : ℝ≥0) ^ (-(1 - β / 2))
          * a ^ ((3 * β / 2) + (β / 2 - 1)) * b ^ (-(3 * β / 2) + (5 * β / 2 - 1)) := by
          rw [← NNReal.rpow_add ha, ← NNReal.rpow_add hb]
      _ = δ ^ (-(ε / 3)) * δ ^ (-2 * β) * δ ^ (2 - β) * (nq : ℝ≥0) ^ (1 - β / 2)
          * (nts : ℝ≥0) ^ (-(1 - β / 2)) * a ^ (2 * β - 1) * b ^ (β - 1) := by
          rw [h_a_expo2, h_b_expo2]
  calc
    δ ^ (-(ε / 3)) * (a / b) ^ (1 - β) * (a⁻¹ * δ) ^ (-2 * β)
        * ((a ^ 2)⁻¹ * δ ^ 2 * ((nq : ℝ≥0) / (nts : ℝ≥0))) ^ (1 - β / 2)
    = δ ^ (-(ε / 3)) * δ ^ (-2 * β) * δ ^ (2 - β) * (nq : ℝ≥0) ^ (1 - β / 2)
        * (nts : ℝ≥0) ^ (-(1 - β / 2)) * a ^ (2 * β - 1) * b ^ (β - 1) := hL
    _ = δ ^ (-(ε / 3)) * δ ^ (-2 * β) * (δ ^ 2 * (nq : ℝ≥0)) ^ (1 - β / 2)
        * (a / b) ^ (3 * β / 2) * b ^ (5 * β / 2 - 1) * ((a * (nts : ℝ≥0)) ^ (1 - β / 2))⁻¹ :=
      hR.symm

/-- **The Proposition 6.6(A) large-`b` combination.**

Given the part-(A) μ-split of Proposition 5.1 (whose inner factor is pre-multiplied), the large-`b`
outer bound `μ(𝒲) ≤ Cout · δ ^ (-ε/3)` from GWZ Lemma 6.9
(`ShadedPlank.multiplicity_le_of_isKatzTao_of_large'`) and the Frostman mass lower bound
`Cm ≤ C_F · |ts| · a` (`Kakeya.volume_plankWindow_le_of_isFrostmanIn`), the part-(A) target follows.

The mass bound is what pays for the `C_F ^ (1-β/2)` of the target: Lemma 6.9's outer bound is
sub-polynomial and carries no `C_F`, while the split's inner factor leaves behind exactly
`((a · |ts|) ^ (1-β/2))⁻¹`, which the mass bound converts into `C_F ^ (1-β/2)` up to the absolute
constant `Cm ^ (-(1-β/2))`. -/
theorem combineLocalFactorFallback {β ε : ℝ} (hβpos : 0 < β) (hβle : β ≤ 1) (hε : 0 < ε)
    {δ a b b₀ Cm Cout Csplit : ℝ≥0}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (ha0 : 0 < a) (hab : a ≤ b) (hb1 : b ≤ 1)
    (hb₀ : 0 < b₀) (hbb₀ : b₀ ≤ b) (hCm : 0 < Cm) (hCs1 : 1 ≤ Csplit)
    {CF : ENNReal} (hCF1 : 1 ≤ CF) (hCFtop : CF ≠ ⊤)
    {nq nts : ℕ} (hnts : nts ≠ 0) (hnq : nq ≠ 0) {μqT μW : ENNReal}
    (hmass : (Cm : ENNReal) ≤ CF * ((nts : ENNReal) * (a : ENNReal)))
    (hW : μW ≤ (Cout : ENNReal) * (δ : ENNReal) ^ (-(ε / 3)))
    (hsplit : μqT ≤ (Csplit : ENNReal) * μW
        * ((δ : ENNReal) ^ (-(ε / 3)) * ((a : ENNReal) / (b : ENNReal)) ^ (1 - β)
          * ((a : ENNReal)⁻¹ * (δ : ENNReal)) ^ (-2 * β)
          * (((a : ENNReal) ^ 2)⁻¹ * (δ : ENNReal) ^ 2 * ((nq : ENNReal) / (nts : ENNReal)))
              ^ (1 - β / 2))) :
    μqT ≤ ((Csplit * Cout * (Cm⁻¹) ^ (1 - β / 2) * max 1 (b₀ ^ (5 * β / 2 - 1)) : ℝ≥0) : ENNReal)
      * ((δ : ENNReal) ^ (-ε) * CF ^ (1 - β / 2)
        * ((a : ENNReal) / (b : ENNReal)) ^ (3 * β / 2)
        * (δ : ENNReal) ^ (-2 * β)
        * ((δ : ENNReal) ^ 2 * (nq : ENNReal)) ^ (1 - β / 2)) := by
  let p : ℝ := 1 - β / 2
  have hp_pos : 0 < p := by dsimp [p]; nlinarith [hβle]
  have hp_nonneg : 0 ≤ p := le_of_lt hp_pos
  have ha0' : a ≠ 0 := ha0.ne'
  have hb0' : b ≠ 0 := (ha0.trans_le hab).ne'
  have hδ0' : δ ≠ 0 := hδ0.ne'
  have hb₀0' : b₀ ≠ 0 := hb₀.ne'
  have hcm0 : Cm ≠ 0 := hCm.ne'
  have hCm0 : (Cm : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hcm0
  have hCmTop : (Cm : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hnts0 : (nts : ℝ≥0) ≠ 0 := by exact_mod_cast hnts
  have hnnq0 : (nq : ℝ≥0) ≠ 0 := by exact_mod_cast hnq
  have hd0e : (δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hδ0'
  have hdte : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hCF0 : CF ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ENNReal) < 1) hCF1)
  -- Step 1: `I` and the combined bound from `hsplit` and `hW`
  let I : ENNReal := (δ : ENNReal) ^ (-(ε / 3)) * ((a : ENNReal) / (b : ENNReal)) ^ (1 - β)
      * ((a : ENNReal)⁻¹ * (δ : ENNReal)) ^ (-2 * β)
      * (((a : ENNReal) ^ 2)⁻¹ * (δ : ENNReal) ^ 2 * ((nq : ENNReal) / (nts : ENNReal)))
          ^ (1 - β / 2)
  have hstep : μqT ≤ (Csplit : ENNReal) * ((Cout : ENNReal) * (δ : ENNReal) ^ (-(ε / 3))) * I := by
    calc
      μqT ≤ (Csplit : ENNReal) * μW * I := by simpa [I] using hsplit
      _ ≤ (Csplit : ENNReal) * ((Cout : ENNReal) * (δ : ENNReal) ^ (-(ε / 3))) * I := by
        gcongr
  -- Step 2: transport the nonnegative-real identity to ENNReal.
  let XL : ℝ≥0 := δ ^ (-(ε / 3)) * (a / b) ^ (1 - β) * (a⁻¹ * δ) ^ (-2 * β)
      * ((a ^ 2)⁻¹ * δ ^ 2 * ((nq : ℝ≥0) / (nts : ℝ≥0))) ^ (1 - β / 2)
  let YR : ℝ≥0 := δ ^ (-(ε / 3)) * δ ^ (-2 * β) * (δ ^ 2 * (nq : ℝ≥0)) ^ (1 - β / 2)
      * (a / b) ^ (3 * β / 2) * b ^ (5 * β / 2 - 1) * ((a * (nts : ℝ≥0)) ^ (1 - β / 2))⁻¹
  have hNN : XL = YR := combineLocalFactorFallbackNN ha0' hb0' hδ0' hnts hnq
  have hntspos : 0 < (nts : ℝ≥0) := by exact_mod_cast (Nat.pos_of_ne_zero hnts)
  have hantpos : 0 < (a * (nts : ℝ≥0) : ℝ≥0) := mul_pos ha0 hntspos
  have hant0 : (a * (nts : ℝ≥0) : ℝ≥0) ≠ 0 := ne_of_gt hantpos
  have hantp0 : (a * (nts : ℝ≥0) : ℝ≥0) ^ (1 - β / 2) ≠ 0 := by
    exact ne_of_gt (NNReal.rpow_pos hantpos)
  have hcoe_lhs : (XL : ENNReal) = I := by
    dsimp [XL, I]
    simp [ENNReal.coe_mul, ENNReal.coe_div hb0', ENNReal.coe_div hnts0,
      ENNReal.coe_inv ha0', ENNReal.coe_inv (pow_ne_zero 2 ha0'),
      ENNReal.coe_rpow_of_ne_zero hδ0',
      ENNReal.coe_rpow_of_ne_zero (div_ne_zero ha0' hb0'),
      ENNReal.coe_rpow_of_ne_zero (mul_ne_zero (inv_ne_zero ha0') hδ0'),
      ENNReal.coe_rpow_of_nonneg ((a ^ 2)⁻¹ * δ ^ 2 * ((nq : ℝ≥0) / (nts : ℝ≥0)))
        (by linarith : 0 ≤ (1 - β / 2 : ℝ))]
  let RE : ENNReal := (δ : ENNReal) ^ (-(ε / 3)) * (δ : ENNReal) ^ (-2 * β)
      * ((δ : ENNReal) ^ 2 * (nq : ENNReal)) ^ (1 - β / 2)
      * ((a : ENNReal) / (b : ENNReal)) ^ (3 * β / 2)
      * (b : ENNReal) ^ (5 * β / 2 - 1)
      * (((a * (nts : ℝ≥0) : ℝ≥0) : ENNReal) ^ (1 - β / 2))⁻¹
  have hcoe_rhs : (YR : ENNReal) = RE := by
    dsimp [YR, RE]
    simp [ENNReal.coe_mul, ENNReal.coe_div hb0',
      ENNReal.coe_rpow_of_ne_zero hδ0',
      ENNReal.coe_rpow_of_ne_zero hb0',
      ENNReal.coe_rpow_of_ne_zero (div_ne_zero ha0' hb0'),
      ENNReal.coe_rpow_of_nonneg (δ ^ 2 * (nq : ℝ≥0))
        (by linarith : 0 ≤ (1 - β / 2 : ℝ)),
      ENNReal.coe_rpow_of_ne_zero hant0,
      ENNReal.coe_inv hantp0]
  have hrew : I = RE := by
    calc
      I = (XL : ENNReal) := hcoe_lhs.symm
      _ = (YR : ENNReal) := by rw [hNN]
      _ = RE := hcoe_rhs
  have hstepQ : μqT ≤ (Csplit : ENNReal) * ((Cout : ENNReal) * (δ : ENNReal) ^ (-(ε / 3))) * RE := by
    rw [hrew] at hstep
    exact hstep
  -- Step 3: the two `δ ^ (-(ε/3))` factors collapse to (at most) `δ ^ (-ε)`
  have hdd : (δ : ENNReal) ^ (-(ε / 3)) * (δ : ENNReal) ^ (-(ε / 3)) ≤ (δ : ENNReal) ^ (-ε) := by
    rw [← ENNReal.rpow_add (-(ε / 3)) (-(ε / 3)) hd0e hdte]
    refine ENNReal.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hδ1) (by linarith)
  -- Step 4: `b ^ (5β/2 - 1) ≤ max 1 (b₀ ^ (5β/2 - 1))`
  let M : ENNReal := (max 1 (b₀ ^ (5 * β / 2 - 1) : ℝ≥0) : ENNReal)
  let e : ℝ := 5 * β / 2 - 1
  have hbpow : (b : ENNReal) ^ e ≤ (max 1 (b₀ ^ e : ℝ≥0) : ENNReal) := by
    by_cases hepos : 0 ≤ e
    · have hb0p : (b : ℝ≥0) ^ e ≤ max 1 (b₀ ^ e : ℝ≥0) := by
        calc
          (b : ℝ≥0) ^ e ≤ (1 : ℝ≥0) ^ e := NNReal.rpow_le_rpow hb1 hepos
          _ = 1 := by simp
          _ ≤ max 1 (b₀ ^ e) := le_max_left _ _
      exact_mod_cast hb0p
    · have hen : e < 0 := lt_of_not_ge hepos
      have hnonneg_m : 0 ≤ -e := by linarith
      have hbig : (b₀ : ENNReal) ^ (-e) ≤ (b : ENNReal) ^ (-e) :=
        ENNReal.rpow_le_rpow (by exact_mod_cast hbb₀) hnonneg_m
      have hinv : ((b : ENNReal) ^ (-e))⁻¹ ≤ ((b₀ : ENNReal) ^ (-e))⁻¹ :=
        (ENNReal.inv_le_inv).mpr hbig
      have heq_b : (b : ENNReal) ^ e = ((b : ENNReal) ^ (-e))⁻¹ := by
        calc
          (b : ENNReal) ^ e = (b : ENNReal) ^ (-(-e)) := by congr 1; ring
          _ = ((b : ENNReal) ^ (-e))⁻¹ := ENNReal.rpow_neg b (-e)
      have heq_b0 : (b₀ : ENNReal) ^ e = ((b₀ : ENNReal) ^ (-e))⁻¹ := by
        calc
          (b₀ : ENNReal) ^ e = (b₀ : ENNReal) ^ (-(-e)) := by congr 1; ring
          _ = ((b₀ : ENNReal) ^ (-e))⁻¹ := ENNReal.rpow_neg b₀ (-e)
      calc
        (b : ENNReal) ^ e ≤ (b₀ : ENNReal) ^ e := by
          rw [heq_b, heq_b0]
          exact hinv
        _ ≤ (max 1 (b₀ ^ e : ℝ≥0) : ENNReal) := by
          exact_mod_cast le_max_right _ _
  have hbpow' : (b : ENNReal) ^ (5 * β / 2 - 1) ≤ M := by
    dsimp [M]
    exact hbpow
  -- Step 4: the Frostman mass bound `((a·nts)^p)⁻¹ ≤ (Cm⁻¹)^p · CF^p`
  let B : ENNReal := ((a * (nts : ℝ≥0) : ℝ≥0) : ENNReal)
  have hBmass : (Cm : ENNReal) ≤ CF * B := by
    calc
      (Cm : ENNReal) ≤ CF * ((nts : ENNReal) * (a : ENNReal)) := hmass
      _ = CF * ((a : ENNReal) * (nts : ENNReal)) := by ring
      _ = CF * B := by
        dsimp [B]
  have hB0 : B ≠ 0 := by
    dsimp [B]
    exact ENNReal.coe_ne_zero.mpr (mul_ne_zero ha0' hnts0)
  have hBte : B ≠ (⊤ : ENNReal) := by dsimp [B]; exact ENNReal.coe_ne_top
  have hpm : 0 ≤ 1 - β / 2 := by linarith [hβle]
  have hpow : (Cm : ENNReal) ^ (1 - β / 2) ≤ CF ^ (1 - β / 2) * B ^ (1 - β / 2) := by
    have h := ENNReal.rpow_le_rpow hBmass hpm
    rwa [ENNReal.mul_rpow_of_nonneg _ _ hpm] at h
  have hCFp0 : CF ^ (1 - β / 2) ≠ 0 := by simp [hCF0, hCFtop]
  have hBp0 : B ^ (1 - β / 2) ≠ 0 := by simp [hB0, hBte]
  have hBpt : B ^ (1 - β / 2) ≠ (⊤ : ENNReal) := ENNReal.rpow_ne_top_of_ne_zero hB0 hBte
  have hCmp0 : (Cm : ENNReal) ^ (1 - β / 2) ≠ 0 := by simp [hCm0, hCmTop]
  have hCmpt : (Cm : ENNReal) ^ (1 - β / 2) ≠ (⊤ : ENNReal) := ENNReal.rpow_ne_top_of_ne_zero hCm0 hCmTop
  have h_small : (Cm : ENNReal) ^ (1 - β / 2) * (B ^ (1 - β / 2))⁻¹ ≤ CF ^ (1 - β / 2) := by
    calc
      (Cm : ENNReal) ^ (1 - β / 2) * (B ^ (1 - β / 2))⁻¹
          ≤ (CF ^ (1 - β / 2) * B ^ (1 - β / 2)) * (B ^ (1 - β / 2))⁻¹ := by
            gcongr
      _ = CF ^ (1 - β / 2) := by
          have hxx : B ^ (1 - β / 2) * (B ^ (1 - β / 2))⁻¹ = 1 := ENNReal.mul_inv_cancel hBp0 hBpt
          calc
            (CF ^ (1 - β / 2) * B ^ (1 - β / 2)) * (B ^ (1 - β / 2))⁻¹
                = CF ^ (1 - β / 2) * (B ^ (1 - β / 2) * (B ^ (1 - β / 2))⁻¹) := by ring
            _ = CF ^ (1 - β / 2) * 1 := by rw [hxx]
            _ = CF ^ (1 - β / 2) := by simp
  have h_big : (B ^ (1 - β / 2))⁻¹ ≤ ((Cm : ENNReal) ^ (1 - β / 2))⁻¹ * CF ^ (1 - β / 2) := by
    calc
      (B ^ (1 - β / 2))⁻¹
          = ((Cm : ENNReal) ^ (1 - β / 2))⁻¹ * ((Cm : ENNReal) ^ (1 - β / 2))
              * (B ^ (1 - β / 2))⁻¹ := by
              rw [ENNReal.inv_mul_cancel hCmp0 hCmpt]
              simp
      _ = ((Cm : ENNReal) ^ (1 - β / 2))⁻¹
              * (((Cm : ENNReal) ^ (1 - β / 2)) * (B ^ (1 - β / 2))⁻¹) := by ring
      _ ≤ ((Cm : ENNReal) ^ (1 - β / 2))⁻¹ * CF ^ (1 - β / 2) := by
            gcongr
  have h_mp_inv : ((Cm : ENNReal) ^ (1 - β / 2))⁻¹ = ((Cm⁻¹ : ℝ≥0) : ENNReal) ^ (1 - β / 2) := by
    rw [← ENNReal.inv_rpow]
    rw [← ENNReal.coe_inv hcm0]
  have hinvmass : (B ^ (1 - β / 2))⁻¹ ≤ ((Cm⁻¹ : ℝ≥0) : ENNReal) ^ (1 - β / 2) * CF ^ (1 - β / 2) := by
    calc
      (B ^ (1 - β / 2))⁻¹ ≤ ((Cm : ENNReal) ^ (1 - β / 2))⁻¹ * CF ^ (1 - β / 2) := h_big
      _ = ((Cm⁻¹ : ℝ≥0) : ENNReal) ^ (1 - β / 2) * CF ^ (1 - β / 2) := by rw [h_mp_inv]
  -- Step 6: assemble
  let δ1 : ENNReal := (δ : ENNReal) ^ (-(ε / 3))
  let δ1' : ENNReal := (δ : ENNReal) ^ (-ε)
  let δ2 : ENNReal := (δ : ENNReal) ^ (-2 * β)
  let Qp : ENNReal := ((δ : ENNReal) ^ 2 * (nq : ENNReal)) ^ (1 - β / 2)
  let F3 : ENNReal := ((a : ENNReal) / (b : ENNReal)) ^ (3 * β / 2)
  have hb1step : μqT ≤ (Csplit : ENNReal) * (Cout : ENNReal) * (δ1 * δ1) * δ2 * Qp * F3
      * (b : ENNReal) ^ (5 * β / 2 - 1) * (B ^ (1 - β / 2))⁻¹ := by
    calc
      μqT ≤ (Csplit : ENNReal) * ((Cout : ENNReal) * δ1) * RE := hstepQ
      _ = (Csplit : ENNReal) * (Cout : ENNReal) * (δ1 * δ1) * δ2 * Qp * F3
          * (b : ENNReal) ^ (5 * β / 2 - 1) * (B ^ (1 - β / 2))⁻¹ := by
        dsimp [RE, δ1, δ2, Qp, F3, B]
        ring
  have hmono1 : (Csplit : ENNReal) * (Cout : ENNReal) * (δ1 * δ1) * δ2 * Qp * F3
        * (b : ENNReal) ^ (5 * β / 2 - 1) * (B ^ (1 - β / 2))⁻¹
      ≤ (Csplit : ENNReal) * (Cout : ENNReal) * δ1' * δ2 * Qp * F3 * M * (B ^ (1 - β / 2))⁻¹ := by
    calc
      (Csplit : ENNReal) * (Cout : ENNReal) * (δ1 * δ1) * δ2 * Qp * F3
            * (b : ENNReal) ^ (5 * β / 2 - 1) * (B ^ (1 - β / 2))⁻¹
          = (Csplit : ENNReal) * (Cout : ENNReal) * δ2 * Qp * F3 * (B ^ (1 - β / 2))⁻¹
              * ((δ1 * δ1) * (b : ENNReal) ^ (5 * β / 2 - 1)) := by ring
      _ ≤ (Csplit : ENNReal) * (Cout : ENNReal) * δ2 * Qp * F3 * (B ^ (1 - β / 2))⁻¹
              * (δ1' * M) := by
            gcongr
      _ = (Csplit : ENNReal) * (Cout : ENNReal) * δ1' * δ2 * Qp * F3 * M * (B ^ (1 - β / 2))⁻¹ := by ring
  have hmono2 : (Csplit : ENNReal) * (Cout : ENNReal) * δ1' * δ2 * Qp * F3 * M * (B ^ (1 - β / 2))⁻¹
      ≤ (Csplit : ENNReal) * (Cout : ENNReal) * δ1' * δ2 * Qp * F3 * M
          * (((Cm⁻¹ : ℝ≥0) : ENNReal) ^ (1 - β / 2) * CF ^ (1 - β / 2)) := by
    calc
      (Csplit : ENNReal) * (Cout : ENNReal) * δ1' * δ2 * Qp * F3 * M * (B ^ (1 - β / 2))⁻¹
          = (Csplit : ENNReal) * (Cout : ENNReal) * δ1' * δ2 * Qp * F3 * M
              * (B ^ (1 - β / 2))⁻¹ := by ring
      _ ≤ (Csplit : ENNReal) * (Cout : ENNReal) * δ1' * δ2 * Qp * F3 * M
              * (((Cm⁻¹ : ℝ≥0) : ENNReal) ^ (1 - β / 2) * CF ^ (1 - β / 2)) := by
            gcongr
      _ = (Csplit : ENNReal) * (Cout : ENNReal) * δ1' * δ2 * Qp * F3 * M
          * (((Cm⁻¹ : ℝ≥0) : ENNReal) ^ (1 - β / 2) * CF ^ (1 - β / 2)) := rfl
  have hmain1 : μqT ≤ (Csplit : ENNReal) * (Cout : ENNReal) * δ1' * δ2 * Qp * F3 * M
      * (((Cm⁻¹ : ℝ≥0) : ENNReal) ^ (1 - β / 2) * CF ^ (1 - β / 2)) :=
    (hb1step.trans hmono1).trans hmono2
  have hgt : (δ : ENNReal) ^ (-ε) * CF ^ (1 - β / 2) * ((a : ENNReal) / (b : ENNReal)) ^ (3 * β / 2)
        * (δ : ENNReal) ^ (-2 * β) * ((δ : ENNReal) ^ 2 * (nq : ENNReal)) ^ (1 - β / 2)
      = δ1' * δ2 * Qp * F3 * CF ^ (1 - β / 2) := by
    dsimp [δ1', δ2, Qp, F3]
    ring
  have hCconst : ((Csplit * Cout * (Cm⁻¹) ^ (1 - β / 2) * max 1 (b₀ ^ (5 * β / 2 - 1)) : ℝ≥0) : ENNReal)
      = (Csplit : ENNReal) * (Cout : ENNReal) * (((Cm⁻¹ : ℝ≥0) : ENNReal) ^ (1 - β / 2)) * M := by
    dsimp [M]
    simp [ENNReal.coe_rpow_of_nonneg (Cm⁻¹ : ℝ≥0)
      (by linarith : 0 ≤ (1 - β / 2 : ℝ))]
  calc
    μqT ≤ (Csplit : ENNReal) * (Cout : ENNReal) * δ1' * δ2 * Qp * F3 * M
        * (((Cm⁻¹ : ℝ≥0) : ENNReal) ^ (1 - β / 2) * CF ^ (1 - β / 2)) := hmain1
    _ = (Csplit : ENNReal) * (Cout : ENNReal) * (((Cm⁻¹ : ℝ≥0) : ENNReal) ^ (1 - β / 2)) * M
        * (δ1' * δ2 * Qp * F3 * CF ^ (1 - β / 2)) := by ring
    _ = ((Csplit * Cout * (Cm⁻¹) ^ (1 - β / 2) * max 1 (b₀ ^ (5 * β / 2 - 1)) : ℝ≥0) : ENNReal)
        * (δ1' * δ2 * Qp * F3 * CF ^ (1 - β / 2)) := by rw [hCconst]
    _ = ((Csplit * Cout * (Cm⁻¹) ^ (1 - β / 2) * max 1 (b₀ ^ (5 * β / 2 - 1)) : ℝ≥0) : ENNReal)
        * ((δ : ENNReal) ^ (-ε) * CF ^ (1 - β / 2) * ((a : ENNReal) / (b : ENNReal)) ^ (3 * β / 2)
          * (δ : ENNReal) ^ (-2 * β) * ((δ : ENNReal) ^ 2 * (nq : ENNReal)) ^ (1 - β / 2)) := by
      rw [hgt]

/-- **The Proposition 6.6(B) large-`b` combination.**

Given the Proposition 5.1 μ-split `μ(𝒯) ≤ Csplit · μ(𝒲) · μ(𝒯_j)`, the large-`b` outer bound
`μ(𝒲) ≤ Cout · δ ^ (-ε/3)` (from `ShadedPlank.multiplicity_le_of_isKatzTao_of_large`), the inner
`γ = 1` plank estimate and the cardinality relation `|ts| · |q_j| ≤ Ccard · |q|`, the part-(B) target
follows.  The `(a/b) ^ β` eccentricity factor is carried by the *inner* bound; the outer bound only
has to be sub-polynomial.

The outer bound is read at the master scale `δ`, which is where GWZ Proposition 5.1 supplies the
outer fullness and Katz--Tao data (see `Kakeya.PlankEstimateAtMasterScale`); a plank-scale bound
`μ(𝒲) ≤ Cout · a ^ (-ε/3)` implies it, since `δ ≤ a`. -/
theorem combineGlobalFactorFallback {β ε : ℝ} (hβpos : 0 < β) (hβle : β ≤ 1) (hε : 0 < ε)
    {δ a b : ℝ≥0} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hδa : δ ≤ a)
    {Cout Csplit Ccard : ℝ≥0} (hCsplit : 1 ≤ Csplit) (hCcard : 1 ≤ Ccard)
    {Δ : ENNReal} {nq nts nj : ℕ} {μqT μW μTj : ENNReal} (hnts : nts ≠ 0)
    (hW : μW ≤ (Cout : ENNReal) * (δ : ENNReal) ^ (-(ε / 3)))
    (hTj : μTj ≤ (δ : ENNReal) ^ (-(ε / 3)) * Δ ^ (1 - β)
        * ((a : ENNReal) / (b : ENNReal)) ^ β * (nj : ENNReal) ^ β)
    (hsplit : μqT ≤ (Csplit : ENNReal) * μW * μTj)
    (hcard : (nts : ENNReal) * (nj : ENNReal) ≤ (Ccard : ENNReal) * (nq : ENNReal)) :
    μqT ≤ ((Csplit * Cout * Ccard ^ β : ℝ≥0) : ENNReal) *
      ((δ : ENNReal) ^ (-ε) * Δ ^ (1 - β)
        * ((a : ENNReal) / (b : ENNReal)) ^ β * (nq : ENNReal) ^ β) := by
  have hd0 : (δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hδ0.ne'
  have hdtop : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  -- 1. transfer the outer bound from `a` to `δ`
  have hAd : (a : ENNReal) ^ (-(ε / 3)) ≤ (δ : ENNReal) ^ (-(ε / 3)) := by
    have hda : (δ : ENNReal) ≤ (a : ENNReal) := by exact_mod_cast hδa
    rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
    exact ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow hda (by positivity))
  have hWd : μW ≤ (Cout : ENNReal) * (δ : ENNReal) ^ (-(ε / 3)) := hW.trans (by gcongr)
  -- 2. the cardinality step
  have hnts1 : (1 : ENNReal) ≤ (nts : ENNReal) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hnts
  have hnj : (nj : ENNReal) ≤ (Ccard : ENNReal) * (nq : ENNReal) :=
    le_trans (by simpa [mul_comm, mul_left_comm] using mul_le_mul_left hnts1 (nj : ENNReal)) hcard
  have hnjpow : (nj : ENNReal) ^ β ≤ (Ccard : ENNReal) ^ β * (nq : ENNReal) ^ β := by
    calc (nj : ENNReal) ^ β ≤ ((Ccard : ENNReal) * (nq : ENNReal)) ^ β :=
          ENNReal.rpow_le_rpow hnj (le_of_lt hβpos)
      _ = (Ccard : ENNReal) ^ β * (nq : ENNReal) ^ β :=
          ENNReal.mul_rpow_of_nonneg _ _ (le_of_lt hβpos)
  -- 3. the two δ-powers
  have hdd : (δ : ENNReal) ^ (-(ε / 3)) * (δ : ENNReal) ^ (-(ε / 3)) ≤ (δ : ENNReal) ^ (-ε) := by
    rw [← ENNReal.rpow_add _ _ hd0 hdtop]
    refine ENNReal.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hδ1) (by linarith)
  -- 4. the coercion of the constant
  have hcoe : ((Csplit * Cout * Ccard ^ β : ℝ≥0) : ENNReal)
      = (Csplit : ENNReal) * (Cout : ENNReal) * (Ccard : ENNReal) ^ β := by
    have hC0 : Ccard ≠ 0 := by
      have : (0 : ℝ≥0) < Ccard := lt_of_lt_of_le zero_lt_one hCcard
      exact this.ne'
    rw [ENNReal.coe_mul, ENNReal.coe_mul, ENNReal.coe_rpow_of_ne_zero hC0]
  -- 5. assemble
  rw [hcoe]
  calc μqT ≤ (Csplit : ENNReal) * μW * μTj := hsplit
    _ ≤ (Csplit : ENNReal) * ((Cout : ENNReal) * (δ : ENNReal) ^ (-(ε / 3)))
        * ((δ : ENNReal) ^ (-(ε / 3)) * Δ ^ (1 - β) * ((a : ENNReal) / (b : ENNReal)) ^ β
            * ((Ccard : ENNReal) ^ β * (nq : ENNReal) ^ β)) := by
        gcongr
        exact hTj.trans (by gcongr)
    _ = ((Csplit : ENNReal) * (Cout : ENNReal) * (Ccard : ENNReal) ^ β)
        * (((δ : ENNReal) ^ (-(ε / 3)) * (δ : ENNReal) ^ (-(ε / 3))) * Δ ^ (1 - β)
            * ((a : ENNReal) / (b : ENNReal)) ^ β * (nq : ENNReal) ^ β) := by ring
    _ ≤ ((Csplit : ENNReal) * (Cout : ENNReal) * (Ccard : ENNReal) ^ β)
        * ((δ : ENNReal) ^ (-ε) * Δ ^ (1 - β)
            * ((a : ENNReal) / (b : ENNReal)) ^ β * (nq : ENNReal) ^ β) := by gcongr

/-- **Absorption for the Proposition 6.6(A) target.**

If the multiplicity of the fine family is at most `δ ^ (-ε)`, the Frostman mass satisfies
`1 ≤ C_F · δ ^ 2 · n` (which is automatic for a family of `δ`-tubes in `B₁`: a single tube gives
`Δ(𝒯, T) ≥ 1 ≤ C_F Δ(𝒯, B₁) ≈ C_F δ ^ 2 n`), and the scales obey `δ ≤ a ≤ b ≤ 1`, then the
Proposition 6.6(A) bound holds:

`μ ≤ δ ^ (-ε) · C_F ^ (1 - β/2) · (a/b) ^ (3β/2) · δ ^ (-2β) · (δ ^ 2 n) ^ (1 - β/2)`.

Two facts make the target weaker than `δ ^ (-ε)`: the Frostman mass makes
`C_F ^ (1-β/2) (δ ^ 2 n) ^ (1-β/2) ≥ 1`, and `δ ≤ a`, `b ≤ 1` give `a/b ≥ δ`, so that
`(a/b) ^ (3β/2) δ ^ (-2β) ≥ δ ^ (3β/2 - 2β) = δ ^ (-β/2) ≥ 1`.

**The hypothesis `δ ≤ a` is essential and is exactly what `Kakeya.coarseSlabFallback` is missing**:
in that statement `a` occurs only in `a ≤ b` and in the conclusion, so `a = 0` makes its right-hand
side `0` while the multiplicity of any family with positive fullness is at least `1`. -/
theorem partATarget_of_multiplicity_le {β ε : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
    {δ a b : ℝ≥0} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hδa : δ ≤ a) (hab : a ≤ b) (hb1 : b ≤ 1)
    {μ CF : ENNReal} {n : ℕ}
    (hmass : 1 ≤ CF * ((δ : ENNReal) ^ 2 * (n : ENNReal)))
    (hμ : μ ≤ (δ : ENNReal) ^ (-ε)) :
    μ ≤ (δ : ENNReal) ^ (-ε) * CF ^ (1 - β / 2)
      * ((a : ENNReal) / (b : ENNReal)) ^ (3 * β / 2)
      * (δ : ENNReal) ^ (-2 * β)
      * ((δ : ENNReal) ^ 2 * (n : ENNReal)) ^ (1 - β / 2) := by
  let p : ℝ := 1 - β / 2
  have hp_pos : 0 < p := by
    dsimp [p]
    nlinarith [hβ1]
  have hp_nonneg : 0 ≤ p := le_of_lt hp_pos
  have hbetaneg : -β / 2 ≤ (0 : ℝ) := by nlinarith [hβ]
  have hb3 : 0 ≤ 3 * β / 2 := by nlinarith [hβ]
  have hδne0 : (δ : ENNReal) ≠ 0 := by exact_mod_cast (ne_of_gt hδ0)
  have hδnetop : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hδ1e : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1
  -- δ ≤ a/b; here b ≤ 1 makes a/b ≥ a ≥ δ
  have hδle : (δ : ENNReal) ≤ (a : ENNReal) / (b : ENNReal) := by
    have ha0 : (a : ENNReal) ≠ 0 := by
      have : (0 : ENNReal) < (a : ENNReal) := by exact_mod_cast (lt_of_lt_of_le hδ0 hδa)
      exact ne_of_gt this
    rw [ENNReal.le_div_iff_mul_le (Or.inr ha0) (Or.inr ENNReal.coe_ne_top)]
    calc
      (δ : ENNReal) * (b : ENNReal) ≤ (δ : ENNReal) * (1 : ENNReal) := by
        exact mul_le_mul le_rfl (by exact_mod_cast hb1) (by positivity) (by positivity)
      _ = (δ : ENNReal) := by simp
      _ ≤ (a : ENNReal) := by exact_mod_cast hδa
  -- Factor 1: C_F ^ p · (δ ^ 2 n) ^ p ≥ 1
  have hfac1 : (1 : ENNReal) ≤ CF ^ p * ((δ : ENNReal) ^ 2 * (n : ENNReal)) ^ p := by
    calc
      (1 : ENNReal) ≤ (CF * ((δ : ENNReal) ^ 2 * (n : ENNReal))) ^ p :=
        ENNReal.one_le_rpow hmass hp_pos
      _ = CF ^ p * ((δ : ENNReal) ^ 2 * (n : ENNReal)) ^ p := by
        rw [ENNReal.mul_rpow_of_nonneg]
        exact hp_nonneg
  -- Factor 2: (a/b) ^ (3β/2) ≥ δ ^ (3β/2)
  have hf2 : (δ : ENNReal) ^ (3 * β / 2) ≤ ((a : ENNReal)/(b : ENNReal)) ^ (3 * β / 2) := by
    exact ENNReal.rpow_le_rpow hδle hb3
  -- Factor 3·4: δ ^ (3β/2) · δ ^ (-2β) = δ ^ (-β/2) ≥ 1
  have hsmall : (1 : ENNReal) ≤ (δ : ENNReal) ^ (3 * β / 2) * (δ : ENNReal) ^ (-2 * β) := by
    have hinv : (1 : ENNReal) ≤ (δ : ENNReal) ^ (-β / 2) := by
      simpa [ENNReal.rpow_zero] using
        (ENNReal.rpow_le_rpow_of_exponent_ge (x := (δ : ENNReal)) hδ1e hbetaneg)
    have hcomb : (δ : ENNReal) ^ (3 * β / 2) * (δ : ENNReal) ^ (-2 * β) =
        (δ : ENNReal) ^ (-β / 2) := by
      have hs : 3 * β / 2 + -2 * β = -β / 2 := by ring
      rw [← ENNReal.rpow_add (3 * β / 2) (-2 * β) hδne0 hδnetop, hs]
    calc
      (1 : ENNReal) ≤ (δ : ENNReal) ^ (-β / 2) := hinv
      _ ≤ (δ : ENNReal) ^ (3 * β / 2) * (δ : ENNReal) ^ (-2 * β) := by
        exact le_of_eq hcomb.symm
  -- Factor 2 with factors 3·4: (a/b)^(3β/2) · δ^(-2β) ≥ 1
  have hfac2 : (1 : ENNReal) ≤
      ((a : ENNReal) / (b : ENNReal)) ^ (3 * β / 2) * (δ : ENNReal) ^ (-2 * β) := by
    calc
      (1 : ENNReal) ≤ (δ : ENNReal) ^ (3 * β / 2) * (δ : ENNReal) ^ (-2 * β) := hsmall
      _ ≤ ((a : ENNReal) / (b : ENNReal)) ^ (3 * β / 2) * (δ : ENNReal) ^ (-2 * β) := by
        exact mul_le_mul hf2 le_rfl (by positivity) (by positivity)
  -- Product of all four factors ≥ 1
  have hbig : (1 : ENNReal) ≤
      CF ^ p * (((a : ENNReal) / (b : ENNReal)) ^ (3 * β / 2) * (δ : ENNReal) ^ (-2 * β))
        * ((δ : ENNReal) ^ 2 * (n : ENNReal)) ^ p := by
    calc
      (1 : ENNReal) = (1 : ENNReal) * 1 := by simp
      _ ≤ (CF ^ p * ((δ : ENNReal) ^ 2 * (n : ENNReal)) ^ p) *
          (((a : ENNReal) / (b : ENNReal)) ^ (3 * β / 2) * (δ : ENNReal) ^ (-2 * β)) := by
        exact mul_le_mul hfac1 hfac2 (by positivity) (by positivity)
      _ = CF ^ p * (((a : ENNReal) / (b : ENNReal)) ^ (3 * β / 2) * (δ : ENNReal) ^ (-2 * β))
          * ((δ : ENNReal) ^ 2 * (n : ENNReal)) ^ p := by
        ring
  calc
    μ ≤ (δ : ENNReal) ^ (-ε) := hμ
    _ ≤ (δ : ENNReal) ^ (-ε) * (CF ^ p * (((a : ENNReal) / (b : ENNReal)) ^ (3 * β / 2)
        * (δ : ENNReal) ^ (-2 * β)) * ((δ : ENNReal) ^ 2 * (n : ENNReal)) ^ p) := by
      exact le_mul_of_one_le_right' hbig
    _ = (δ : ENNReal) ^ (-ε) * CF ^ (1 - β / 2) * ((a : ENNReal) / (b : ENNReal)) ^ (3 * β / 2)
        * (δ : ENNReal) ^ (-2 * β) * ((δ : ENNReal) ^ 2 * (n : ENNReal)) ^ (1 - β / 2) := by
      dsimp [p]
      ring

/-- **Absorption for the Proposition 6.6(B) target.**

`Δ_max ≥ 1` and `n ≥ 1` make the factors `Δ_max ^ (1-β)` and `n ^ β` harmless, so the
Proposition 6.6(B) bound follows from a multiplicity bound *which already carries the eccentricity
factor*, `μ ≤ δ ^ (-ε) (a/b) ^ β`.

This is the precise sense in which part (B) differs from part (A): its target has no `δ ^ (-2β)`
factor to pay for `(a/b) ^ β`, so a sub-polynomial bound such as Lemma 6.9's `μ ≲ δ ^ (-3η)` does
*not* imply it — `(a/b) ^ β` can be as small as `δ ^ β`.  In the paper's argument the eccentricity
factor is produced by the `γ = 1` application of GWZ Lemma 6.1 to the *inner*, rescaled family, and
Lemma 6.9 replaces only the *outer* application; so the part-(B) fallback needs the
Proposition 5.1 μ-split as well, not Lemma 6.9 alone. -/
theorem partBTarget_of_multiplicity_le {β ε : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
    {δ a b : ℝ≥0} {μ Δ : ENNReal} {n : ℕ} (hΔ : 1 ≤ Δ) (hn : 1 ≤ n)
    (hμ : μ ≤ (δ : ENNReal) ^ (-ε) * ((a : ENNReal) / (b : ENNReal)) ^ β) :
    μ ≤ (δ : ENNReal) ^ (-ε) * Δ ^ (1 - β)
      * ((a : ENNReal) / (b : ENNReal)) ^ β * (n : ENNReal) ^ β := by
  let A : ENNReal := (δ : ENNReal) ^ (-ε)
  let B : ENNReal := ((a : ENNReal) / (b : ENNReal)) ^ β
  let C : ENNReal := Δ ^ (1 - β)
  let D : ENNReal := (n : ENNReal) ^ β
  have hC : 1 ≤ C := by
    dsimp [C]
    have h0 : 0 ≤ 1 - β := by linarith
    rw [← ENNReal.one_rpow (1 - β)]
    exact ENNReal.rpow_le_rpow hΔ h0
  have hD : 1 ≤ D := by
    dsimp [D]
    exact ENNReal.one_le_rpow (by exact_mod_cast hn) hβ
  have hmain : A * B ≤ A * C * B * D := by
    calc
      A * B = A * B * 1 := by ring
      _ ≤ A * B * C := mul_le_mul_right hC (A * B)
      _ = A * C * B := by ring
      _ = A * C * B * 1 := by ring
      _ ≤ A * C * B * D := mul_le_mul_right hD (A * C * B)
  simpa using (le_trans hμ hmain)

end Kakeya

end

end

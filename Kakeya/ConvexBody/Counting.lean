/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.ConvexBody
public import Kakeya.DimensionN.Prism
public import Kakeya.DimensionThree.Slab.Normalization
public import Kakeya.Mathlib.Geometry.Cylinder
public import Kakeya.Thickness.Volume
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Convex.Measure
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Counting essentially distinct convex bodies of large volume in a prism

This file records the general convex geometry behind the *subfamily selection* of the plank
presentation (blueprint `lem:ml2plankSubfamilySelection`): inside a rectangular prism `R` of
positive volume only boundedly many pairwise essentially distinct compact convex bodies of
volume `≥ α |R|` fit, the bound depending on the ambient dimension and on `α` alone
(`Kakeya.card_le_of_pairwise_essDistinct_in_prism`).

The route is the one the blueprint prescribes, and it is *not* the one used for `δ`-tubes in
`Kakeya/Tube/CardEssentiallyDistinct.lean`: a general convex body has no two-point
parametrisation to discretise, so the lattice count there is replaced by a Hausdorff
separation argument. A body of volume `≥ α |R|` contains a ball of a fixed radius
`ρ(n, α)` (`Kakeya.exists_closedBall_subset_of_le_volume`); two essentially distinct bodies
with such an inner ball cannot be Hausdorff-close (`Kakeya.hausdorff_separated_of_essDistinct`);
and a family of pairwise Hausdorff-separated sets inside a bounded set is finite, with an
explicit bound coming from any cover by small pieces
(`Kakeya.card_le_of_pairwise_not_close_of_cover`, `Kakeya.exists_cover_dist_le`; the
`Metric.diam`-phrased variants are unusable, see the note below on the deleted
`Kakeya.card_le_of_pairwise_not_hausdorff_close`).

Two statements here would classically rest on convex geometry that Mathlib does not have
(Steinhagen's inequality, respectively Brunn's theorem and Grünbaum's centroid inequality):

* `Kakeya.exists_closedBall_subset_of_le_volume` (blueprint `lem:convexInnerBallVolume`);
* `Kakeya.exists_essOverlapDilate_constant` (blueprint `lem:essOverlapDilate`).

Both are nevertheless **proved** here, from one elementary and affinely equivariant device
instead: the *maximal-volume inscribed simplex* of a convex body of positive volume
(the private `exists_maximal_frame` below). Maximality of its volume says exactly that every
point of the body has all its barycentric coordinates with respect to that simplex in
`[-1, 1]`, and both statements follow from that single fact by determinant and slab
computations — for the first at precisely the constant `2 (n+1)` the blueprint displays.

The blueprint notes that all of this is general convex geometry with no Kakeya content and
belongs in the convex-body chapter; that is why it lives here and not in the non-slab files.
-/

@[expose] public section

open Finset MeasureTheory Metric Set
open scoped NNReal Pointwise Real RealInnerProductSpace

noncomputable section

namespace Kakeya

/-! ### Prisms -/

variable {n : ℕ} {E S : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [PseudoMetricSpace S] [NormedAddTorsor E S]

/-- **A prism lies in the Euclidean ball of its half-widths** (blueprint
`lem:prismSubsetClosedBallEuclidean`).

This is the Euclidean companion of the `ℓ¹` bound `PrismNDim.carrier_subset_closedBall`, whose
radius is `∑ i, w i`. The gain matters: for a plank of half-widths `a' × b' × 1` with
`a' ≤ b' ≤ 1` the `ℓ¹` radius is at most `3` while the Euclidean radius is at most `√3`, and
only the latter fits the recentred enclosing box into the Section 6 window of radius `4`
(`Kakeya.VeryNotSticky.plankRecentredWindow`).

The proof is Parseval for the orthonormal frame of the prism, which is a basis of the whole
space. -/
theorem _root_.PrismNDim.carrier_subset_closedBall_euclidean (P : PrismNDim n E S) :
    (P.carrier : Set S) ⊆
      closedBall P.center (Real.sqrt (∑ i, (P.thicknesses i : ℝ) ^ 2)) := by
  intro x hx
  rw [P.mem_carrier_iff] at hx
  rw [Metric.mem_closedBall, dist_eq_norm_vsub E]
  refine Real.le_sqrt_of_sq_le ?_
  rw [← P.basis.sum_sq_inner_left (x -ᵥ P.center)]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [real_inner_comm, ← P.basis.repr_apply_apply (x -ᵥ P.center) i]
  exact sq_le_sq' (abs_le.mp (hx i)).1 (abs_le.mp (hx i)).2

/-- **A dilate about an interior point sits in a concentric dilate** (blueprint
`lem:prismDilateAboutPoint`).

`z + λ (P - z) ⊆ (2λ - 1) P` for every `z ∈ P` and every `λ ≥ 1`, the right-hand side being
`PrismNDim.dilation`, i.e. the prism with the same centre and frame and all half-widths
multiplied by `2λ - 1`. -/
theorem _root_.PrismNDim.homothety_image_subset_dilation (P : PrismNDim n E S) {z : S}
    (hz : z ∈ (P.carrier : Set S)) {lam : NNReal} (hlam : 1 ≤ lam) :
    (AffineMap.homothety z (lam : ℝ)) '' (P.carrier : Set S) ⊆
      ((P.dilation (2 * lam - 1)).carrier : Set S) := by
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  rw [P.dilation_eq_resize]
  rw [P.mem_resize_carrier (fun i => (2 * lam - 1) * P.thicknesses i)]
  intro i
  have hxcomp : |P.basis.repr (x -ᵥ P.center) i| ≤ (P.thicknesses i : ℝ) :=
    (P.mem_carrier_iff x).1 hx i
  have hzcomp : |P.basis.repr (z -ᵥ P.center) i| ≤ (P.thicknesses i : ℝ) :=
    (P.mem_carrier_iff z).1 hz i
  have hlampos : (0 : ℝ) < (lam : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hlam)
  have hlam1 : (1 : ℝ) ≤ (lam : ℝ) := by exact_mod_cast hlam
  have hlam0 : (0 : ℝ≥0) ≤ lam := le_trans zero_le_one hlam
  have hv : AffineMap.homothety z (lam : ℝ) x -ᵥ P.center
      = (lam : ℝ) • (x -ᵥ P.center) + (1 - (lam : ℝ)) • (z -ᵥ P.center) := by
    rw [AffineMap.homothety_apply]
    rw [vadd_vsub_assoc]
    rw [← vsub_sub_vsub_cancel_right x z P.center]
    rw [smul_sub]
    rw [sub_smul, one_smul]
    -- lam•u - lam•v + v = lam•u + (v - lam•v), same by abelian group laws
    abel
  have hcomm : P.basis.repr (AffineMap.homothety z (lam : ℝ) x -ᵥ P.center) i
      = (lam : ℝ) * P.basis.repr (x -ᵥ P.center) i
          + (1 - (lam : ℝ)) * P.basis.repr (z -ᵥ P.center) i := by
    rw [hv]
    simp only [map_add, map_smul, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  calc
    |P.basis.repr (AffineMap.homothety z (lam : ℝ) x -ᵥ P.center) i|
        = |(lam : ℝ) * P.basis.repr (x -ᵥ P.center) i
            + (1 - (lam : ℝ)) * P.basis.repr (z -ᵥ P.center) i| := by rw [hcomm]
    _ ≤ |(lam : ℝ) * P.basis.repr (x -ᵥ P.center) i|
        + |(1 - (lam : ℝ)) * P.basis.repr (z -ᵥ P.center) i| := by
          exact abs_add_le _ _
    _ = (lam : ℝ) * |P.basis.repr (x -ᵥ P.center) i|
        + ((lam : ℝ) - 1) * |P.basis.repr (z -ᵥ P.center) i| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (le_of_lt hlampos)]
          have hsl : |(1 : ℝ) - (lam : ℝ)| = (lam : ℝ) - 1 := by
            rw [abs_of_nonpos (sub_nonpos.mpr hlam1)]
            ring
          rw [hsl]
    _ ≤ (lam : ℝ) * (P.thicknesses i : ℝ)
        + ((lam : ℝ) - 1) * (P.thicknesses i : ℝ) := by
          exact add_le_add (mul_le_mul_of_nonneg_left hxcomp (le_of_lt hlampos))
            (mul_le_mul_of_nonneg_left hzcomp (sub_nonneg.mpr hlam1))
    _ = (2 * (lam : ℝ) - 1) * (P.thicknesses i : ℝ) := by ring
    _ = ((2 * lam - 1 : ℝ≥0) : ℝ) * (P.thicknesses i : ℝ) := by
          have hcoef : ((2 * lam - 1 : ℝ≥0) : ℝ) = 2 * (lam : ℝ) - 1 := by
            rw [NNReal.coe_sub]
            · rw [NNReal.coe_mul, NNReal.coe_two, NNReal.coe_one]
            · exact le_trans hlam (le_mul_of_one_le_left hlam0 one_le_two)
          rw [hcoef]

/-- **A prism of positive volume is an affine copy of the cube** (blueprint
`lem:prismAffineToCube`).

The normalising map `T x = (⟨x - c, b i⟩ / w i)ᵢ` carries `R` onto the cube of half-widths `1`
in the frame of `R`, and multiplies every volume by the single factor `2 ^ n / |R|`. The
conclusion is stated in the product form `|R| · |T A| = 2 ^ n · |A|` so that no division in
`ENNReal` occurs.

Positivity of `|R|` is what forces every half-width to be nonzero, hence `T` to be
invertible. -/
theorem _root_.PrismNDim.exists_affineEquiv_image_eq_cube
    (R : PrismNDim n (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)))
    (hR : 0 < volume (R.carrier : Set (EuclideanSpace ℝ (Fin n)))) :
    ∃ T : EuclideanSpace ℝ (Fin n) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin n),
      T '' (R.carrier : Set (EuclideanSpace ℝ (Fin n))) =
        ((PrismNDim.mk' (0 : EuclideanSpace ℝ (Fin n)) R.basis (fun _ => (1 : NNReal))).carrier :
          Set (EuclideanSpace ℝ (Fin n))) ∧
      ∀ A : Set (EuclideanSpace ℝ (Fin n)),
        volume (R.carrier : Set (EuclideanSpace ℝ (Fin n))) * volume (T '' A) =
          2 ^ n * volume A := by
  classical
  set c : NNReal := ∏ i, R.thicknesses i with hc
  have hvolR : volume (R.carrier : Set (EuclideanSpace ℝ (Fin n))) = 2 ^ n * (c : ENNReal) := by
    rw [PrismNDim.volume_carrier, finrank_euclideanSpace_fin, hc,
      ENNReal.ofNNReal_finsetProd]
  have hc0 : c ≠ 0 := by
    intro h
    rw [hvolR, h] at hR
    simp at hR
  have hwpos : ∀ i, (0 : ℝ) < (R.thicknesses i : ℝ) := by
    intro i
    have : R.thicknesses i ≠ 0 := by
      intro h
      exact hc0 (by rw [hc, Finset.prod_eq_zero (Finset.mem_univ i) h])
    exact lt_of_le_of_ne (R.thicknesses i).coe_nonneg (Ne.symm (by
      simpa [NNReal.coe_eq_zero] using this))
  set r : Fin n → ℝ := fun i => ((R.thicknesses i : ℝ))⁻¹ with hrdef
  have hr : ∀ i, r i ≠ 0 := fun i => inv_ne_zero (ne_of_gt (hwpos i))
  refine ⟨Kakeya.frameScaling R.center R.basis r hr, ?_, ?_⟩
  · have hthick : (fun i => Real.toNNReal |r i| * R.thicknesses i) = (fun _ => (1 : NNReal)) := by
      funext i
      have hpos : (0 : ℝ) < r i := by rw [hrdef]; exact inv_pos.mpr (hwpos i)
      apply NNReal.coe_inj.mp
      push_cast
      rw [Real.coe_toNNReal _ (abs_nonneg (r i)), abs_of_pos hpos, hrdef]
      field_simp
      exact div_self (ne_of_gt (hwpos i))
    rw [Kakeya.frameScaling_image_prism R r hr, hthick]
  · intro A
    rw [Kakeya.volume_image_affineEquiv, Kakeya.affineJacobian_frameScaling]
    have hprod : ∏ i, r i = ((c : ℝ))⁻¹ := by
      rw [hrdef, hc]
      push_cast
      rw [← Finset.prod_inv_distrib]
    have hcpos : (0 : ℝ) < (c : ℝ) := by
      rw [hc]
      push_cast
      exact Finset.prod_pos (fun i _ => hwpos i)
    rw [hprod, abs_of_pos (inv_pos.mpr hcpos)]
    have hofr : ENNReal.ofReal ((c : ℝ))⁻¹ = ((c⁻¹ : NNReal) : ENNReal) := by
      rw [← NNReal.coe_inv, ENNReal.ofReal_coe_nnreal]
    rw [hofr, hvolR]
    have hcancel : (c : ENNReal) * ((c⁻¹ : NNReal) : ENNReal) = 1 := by
      rw [← ENNReal.coe_mul, mul_inv_cancel₀ hc0, ENNReal.coe_one]
    calc 2 ^ n * (c : ENNReal) * (((c⁻¹ : NNReal) : ENNReal) * volume A)
        = 2 ^ n * ((c : ENNReal) * ((c⁻¹ : NNReal) : ENNReal)) * volume A := by ring
      _ = 2 ^ n * volume A := by rw [hcancel, mul_one]


/-! ### Inner balls, Hausdorff closeness and essential distinctness -/

variable {m : ℕ}

/-! #### The maximal-simplex construction behind `Kakeya.exists_closedBall_subset_of_le_volume`

The inner-ball lemma below is proved by the classical *maximal simplex* argument, which needs no
convex geometry beyond determinants: among all `(m+1)`-tuples of points of `K`, pick one whose
simplex has maximal volume (equivalently, maximal homogenised determinant). Maximality says
exactly that every point of `K` has all its barycentric coordinates with respect to that simplex
in `[-1, 1]`, so `K` lies in a slab of half-width `h_j` about each facet hyperplane, whence
`h_j ≥ v / (2 (2ϱ)^{m-1})`; and the centroid of the simplex is at barycentric distance
`1 / (m+1)` from every facet. -/

section InnerBallSlab

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

/-- The volume of a closed ball of radius `r` is at most `(2r)^n`. -/
private lemma volume_closedBall_le_two_mul_pow (r : ℝ) (hr : 0 ≤ r) :
    volume (closedBall (0 : F) r) ≤ ENNReal.ofReal ((2 * r) ^ (Module.finrank ℝ F)) := by
  rw [Measure.addHaar_closedBall' volume (0 : F) hr]
  calc
    ENNReal.ofReal (r ^ Module.finrank ℝ F) * volume (closedBall (0 : F) 1)
        ≤ ENNReal.ofReal (r ^ Module.finrank ℝ F) * 2 ^ Module.finrank ℝ F := by
          gcongr
          exact volume_closedBall_le_two_pow_finrank (E := F)
    _ = ENNReal.ofReal ((2 * r) ^ Module.finrank ℝ F) := by
      rw [ENNReal.ofReal_pow hr, ← mul_pow,
        ENNReal.ofReal_pow (mul_nonneg (by positivity) hr),
        ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2)]
      norm_num [mul_comm]

/-- A set inside a ball of radius `ϱ` whose inner products with a unit vector `u` lie in
`[a, b]` has volume at most `(b - a) (2ϱ)^{n-1}`. -/
private lemma volume_le_of_inner_mem_Icc_of_subset_ball {u : F} (hu : ‖u‖ = 1) {S : Set F}
    {ϱ a b : ℝ} (hϱ : 0 ≤ ϱ) (hball : S ⊆ closedBall (0 : F) ϱ)
    (hslab : ∀ x ∈ S, (inner ℝ x u : ℝ) ∈ Set.Icc a b) :
    volume S ≤ ENNReal.ofReal (b - a) *
      ENNReal.ofReal ((2 * ϱ) ^ (Module.finrank ℝ F - 1)) := by
  have hune : u ≠ 0 := by rw [← norm_ne_zero_iff, hu]; norm_num
  have hfr : Module.finrank ℝ ((ℝ ∙ u)ᗮ : Submodule ℝ F) = Module.finrank ℝ F - 1 := by
    have h1 := Submodule.finrank_add_finrank_orthogonal (𝕜 := ℝ) (ℝ ∙ u)
    have h2 : Module.finrank ℝ (ℝ ∙ u) = 1 := finrank_span_singleton hune
    omega
  have hsub : S ⊆ cylinder 0 u a b ϱ := by
    intro x hx
    refine ⟨by simpa using hslab x hx, ?_⟩
    have hxb : ‖x‖ ≤ ϱ := by simpa [dist_eq_norm] using hball hx
    have hsq : ‖x - (inner ℝ x u : ℝ) • u‖ ^ 2 ≤ ‖x‖ ^ 2 := by
      rw [norm_sub_sq_real, norm_smul, real_inner_smul_right]
      simp only [hu, Real.norm_eq_abs, mul_one, sq_abs]
      nlinarith [sq_nonneg (inner ℝ x u : ℝ)]
    have hle : ‖x - (inner ℝ x u : ℝ) • u‖ ≤ ‖x‖ :=
      (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq
    simpa using hle.trans hxb
  calc volume S ≤ volume (cylinder (0 : F) u a b ϱ) := measure_mono hsub
    _ = ENNReal.ofReal (b - a) * volume (closedBall (0 : ((ℝ ∙ u)ᗮ : Submodule ℝ F)) ϱ) :=
        volume_cylinder hu 0 a b ϱ
    _ ≤ ENNReal.ofReal (b - a) * ENNReal.ofReal ((2 * ϱ) ^ (Module.finrank ℝ F - 1)) := by
        gcongr
        have := volume_closedBall_le_two_mul_pow (F := ((ℝ ∙ u)ᗮ : Submodule ℝ F)) ϱ hϱ
        rwa [hfr] at this


end InnerBallSlab

section InnerBallSimplex

local notation "Eu" => EuclideanSpace ℝ (Fin m)
local notation "Vh" => (Fin (m + 1) → ℝ)

/-- Homogenisation: `x ↦ (1, x)`. -/
private def homogenize (x : Eu) : Vh := Fin.cons 1 (fun i => x i)

private lemma homogenize_zero (x : Eu) : homogenize x 0 = 1 := by simp [homogenize]
private lemma homogenize_succ (x : Eu) (i : Fin m) : homogenize x i.succ = x i := by
  simp [homogenize]

/-- The homogenisation of an affine combination. -/
private lemma homogenize_comb {c : Fin (m + 1) → ℝ} {p : Fin (m + 1) → Eu} {x : Eu}
    (h1 : ∑ j, c j = 1) (h2 : ∑ j, c j • p j = x) :
    ∑ j, c j • homogenize (p j) = homogenize x := by
  funext k
  rw [Finset.sum_apply]
  induction k using Fin.cases with
  | zero => simpa [homogenize_zero] using h1
  | succ i =>
      simp only [Pi.smul_apply, smul_eq_mul, homogenize_succ]
      rw [← h2]
      simp [Finset.sum_apply]

/-- Reading off an affine combination from a homogeneous linear combination. -/
private lemma of_homogenize_comb {c : Fin (m + 1) → ℝ} {p : Fin (m + 1) → Eu} {x : Eu}
    (h : ∑ j, c j • homogenize (p j) = homogenize x) :
    (∑ j, c j) = 1 ∧ ∑ j, c j • p j = x := by
  constructor
  · have := congrFun h 0
    rw [Finset.sum_apply] at this
    simpa [homogenize_zero] using this
  · refine PiLp.ext fun i => ?_
    have := congrFun h i.succ
    rw [Finset.sum_apply] at this
    simp only [Pi.smul_apply, smul_eq_mul, homogenize_succ] at this
    simpa [Finset.sum_apply] using this

/-- The determinant attached to an `(m + 1)`-tuple of points: the determinant of the
homogenised family. -/
private def detHomogenize (q : Fin (m + 1) → Eu) : ℝ :=
  (Pi.basisFun ℝ (Fin (m + 1))).det (fun j => homogenize (q j))

private lemma detHomogenize_eq_det (q : Fin (m + 1) → Eu) :
    detHomogenize q
      = (Matrix.of fun i j => homogenize (q j) i : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ).det := by
  rw [detHomogenize, Module.Basis.det_apply]
  rfl

private lemma continuous_detHomogenize :
    Continuous (fun q : Fin (m + 1) → Eu => detHomogenize q) := by
  have hmat : Continuous fun q : Fin (m + 1) → Eu =>
      (Matrix.of fun i j => homogenize (q j) i : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) := by
    refine continuous_matrix fun i j => ?_
    simp only [Matrix.of_apply]
    induction i using Fin.cases with
    | zero => simpa only [homogenize_zero] using continuous_const
    | succ i' =>
        simp only [homogenize_succ]
        exact (EuclideanSpace.proj i').continuous.comp (continuous_apply j)
  simpa only [funext detHomogenize_eq_det] using hmat.matrix_det

/-- A tuple with nonzero homogenised determinant exists inside any set containing a ball. -/
private lemma exists_detHomogenize_ne_zero {S : Set Eu} {z : Eu} {ε : ℝ} (hε : 0 < ε)
    (hball : closedBall z ε ⊆ S) :
    ∃ q : Fin (m + 1) → Eu, (∀ j, q j ∈ S) ∧ detHomogenize q ≠ 0 := by
  classical
  refine ⟨Fin.cons z (fun i => z + ε • EuclideanSpace.single i (1:ℝ)), ?_, ?_⟩
  · intro j
    induction j using Fin.cases with
    | zero =>
        simp only [Fin.cons_zero]
        exact hball (mem_closedBall_self hε.le)
    | succ i =>
        simp only [Fin.cons_succ]
        refine hball ?_
        rw [mem_closedBall, dist_eq_norm]
        simp [norm_smul, abs_of_pos hε, PiLp.norm_single]
  · -- linear independence of the homogenised family
    set q : Fin (m + 1) → Eu := Fin.cons z (fun i => z + ε • EuclideanSpace.single i (1:ℝ)) with hq
    have hli : LinearIndependent ℝ (fun j => homogenize (q j)) := by
      rw [Fintype.linearIndependent_iff]
      intro c hc
      have h0 : ∑ j, c j = 0 := by
        have := congrFun hc 0
        rw [Finset.sum_apply] at this
        simpa [homogenize_zero] using this
      have hqi : ∀ (j : Fin (m + 1)) (i : Fin m),
          (q j) i = z i + ε * (if j = i.succ then 1 else 0) := by
        intro j i
        induction j using Fin.cases with
        | zero => simp [hq, (Fin.succ_ne_zero i).symm]
        | succ k =>
            simp [hq, Fin.succ_inj, eq_comm]
      have hi : ∀ i : Fin m, c i.succ = 0 := by
        intro i
        have hce := congrFun hc i.succ
        rw [Finset.sum_apply] at hce
        simp only [Pi.smul_apply, smul_eq_mul, homogenize_succ] at hce
        have hexp : ∑ j, c j * (q j) i = (∑ j, c j) * z i + ε * c i.succ := by
          have : ∀ j : Fin (m + 1), c j * (q j) i
              = c j * z i + ε * (if j = i.succ then c j else 0) := by
            intro j
            rw [hqi j i]
            by_cases h : j = i.succ
            · simp [h]
              ring
            · simp [h]
          rw [Finset.sum_congr rfl (fun j _ => this j), Finset.sum_add_distrib,
            ← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_ite_eq' Finset.univ i.succ c]
          simp
        rw [hexp] at hce
        simp only [Pi.zero_apply] at hce
        rw [h0, zero_mul, zero_add] at hce
        exact (mul_eq_zero.mp hce).resolve_left (ne_of_gt hε)
      intro j
      induction j using Fin.cases with
      | zero =>
          have hs : ∑ j, c j = c 0 := by
            rw [Fin.sum_univ_succ]
            simp [hi]
          linarith [hs, h0]
      | succ i => exact hi i
    have hcard : Fintype.card (Fin (m + 1)) = Module.finrank ℝ (Fin (m + 1) → ℝ) := by simp
    have hB : ⇑(basisOfLinearIndependentOfCardEqFinrank hli hcard) = fun j => homogenize (q j) :=
      coe_basisOfLinearIndependentOfCardEqFinrank hli hcard
    have hu := (Pi.basisFun ℝ (Fin (m + 1))).isUnit_det
      (basisOfLinearIndependentOfCardEqFinrank hli hcard)
    rw [hB] at hu
    exact hu.ne_zero

/-- A maximiser of `|detHomogenize|` over tuples in a nonempty compact set. -/
private lemma exists_max_detHomogenize {S : Set Eu} (hcomp : IsCompact S) (hne : S.Nonempty) :
    ∃ p : Fin (m + 1) → Eu, (∀ j, p j ∈ S) ∧
      ∀ q : Fin (m + 1) → Eu, (∀ j, q j ∈ S) → |detHomogenize q| ≤ |detHomogenize p| := by
  classical
  set T : Set (Fin (m + 1) → Eu) := Set.pi Set.univ (fun _ => S) with hT
  have hTc : IsCompact T := isCompact_univ_pi fun _ => hcomp
  obtain ⟨z, hz⟩ := hne
  have hTne : T.Nonempty := ⟨fun _ => z, fun j _ => hz⟩
  obtain ⟨p, hpT, hmax⟩ :=
    hTc.exists_isMaxOn hTne (continuous_detHomogenize.abs.continuousOn)
  refine ⟨p, fun j => hpT j (Set.mem_univ j), fun q hq => ?_⟩
  exact hmax (fun j _ => hq j)

/-- **Cramer step**: replacing the `j`-th point by `x` multiplies the homogenised determinant
by the `j`-th barycentric weight of `x`. -/
private lemma detHomogenize_update (p : Fin (m + 1) → Eu) (j : Fin (m + 1)) (x : Eu)
    (c : Fin (m + 1) → ℝ) (hc : ∑ i, c i • homogenize (p i) = homogenize x) :
    detHomogenize (Function.update p j x) = c j * detHomogenize p := by
  classical
  set w : Fin (m + 1) → Vh := fun k => homogenize (p k) with hw
  have hupd : (fun k => homogenize (Function.update p j x k))
      = Function.update w j (homogenize x) := by
    funext k
    by_cases h : k = j
    · subst h; simp [hw]
    · simp [hw, Function.update_of_ne h]
  have hdet : detHomogenize (Function.update p j x)
      = (Pi.basisFun ℝ (Fin (m + 1))).det (Function.update w j (homogenize x)) := by
    rw [detHomogenize, hupd]
  rw [hdet, ← hc, AlternatingMap.map_update_sum]
  have hterm : ∀ i : Fin (m + 1),
      (Pi.basisFun ℝ (Fin (m + 1))).det (Function.update w j (c i • w i))
        = if i = j then c j * detHomogenize p else 0 := by
    intro i
    rw [AlternatingMap.map_update_smul]
    by_cases h : i = j
    · subst h
      simp [Function.update_eq_self, detHomogenize, hw]
    · have hz : (Pi.basisFun ℝ (Fin (m + 1))).det (Function.update w j (w i)) = 0 := by
        refine AlternatingMap.map_eq_zero_of_eq _ _ ?_ h
        rw [Function.update_of_ne h, Function.update_self]
      rw [hz, smul_zero, if_neg h]
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  simp

/-- The linear part of the homogenisation. -/
private def homogenizeL : Eu →ₗ[ℝ] Vh where
  toFun x := Fin.cons 0 (fun i => x i)
  map_add' x y := by
    funext k
    induction k using Fin.cases with
    | zero => simp
    | succ i => simp
  map_smul' r x := by
    funext k
    induction k using Fin.cases with
    | zero => simp
    | succ i => simp

private lemma homogenize_sub (x y : Eu) : homogenize x - homogenize y = homogenizeL (x - y) := by
  funext k
  induction k using Fin.cases with
  | zero => simp [homogenize, homogenizeL]
  | succ i => simp [homogenize, homogenizeL]

/-- **The maximal simplex frame of a convex body of positive volume.**

Among all `(m + 1)`-tuples of points of `K` choose one maximising the homogenised determinant.
It is an affine basis, and maximality says exactly that every point of `K` has all its
barycentric coordinates with respect to it in `[-1, 1]`. -/
private lemma exists_maximal_frame (K : ConvexSpaceBody Eu) (hvolpos : 0 < volume K.carrier) :
    ∃ (p : Fin (m + 1) → Eu) (lam : Eu → Fin (m + 1) → ℝ) (Lin : Fin (m + 1) → (Eu →ₗ[ℝ] ℝ)),
      (∀ j, p j ∈ K.carrier) ∧
      (∀ x, (∑ j, lam x j) = 1) ∧
      (∀ x, ∑ j, lam x j • p j = x) ∧
      (∀ x ∈ K.carrier, ∀ j, |lam x j| ≤ 1) ∧
      (∀ (c : Fin (m + 1) → ℝ) (x : Eu), (∑ k, c k) = 1 → (∑ k, c k • p k) = x →
        ∀ j, lam x j = c j) ∧
      (∀ x y j, lam x j = lam y j + Lin j (x - y)) := by
  classical
  have hKconv : Convex ℝ K.carrier := K.convex
  -- `K` has nonempty interior, else it lies in a proper affine subspace and is null
  have hint : (interior K.carrier).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have hspan : affineSpan ℝ K.carrier ≠ ⊤ := by
      intro hsp
      rw [← Set.not_nonempty_iff_eq_empty] at h
      exact h (Convex.interior_nonempty_iff_affineSpan_eq_top hKconv |>.mpr hsp)
    have hnull : volume K.carrier = 0 :=
      measure_mono_null (subset_affineSpan ℝ _)
        (Measure.addHaar_affineSubspace volume _ hspan)
    exact absurd hnull hvolpos.ne'
  obtain ⟨z0, hz0⟩ := hint
  obtain ⟨ε, hε, hballz⟩ := Metric.isOpen_iff.mp isOpen_interior z0 hz0
  obtain ⟨q, hqK, hqdet⟩ := exists_detHomogenize_ne_zero (S := K.carrier) (z := z0) (ε := ε/2)
    (by linarith)
    ((closedBall_subset_ball (by linarith)).trans (hballz.trans interior_subset))
  obtain ⟨p, hpK, hpmax⟩ := exists_max_detHomogenize K.isCompact ⟨z0, interior_subset hz0⟩
  have hD : detHomogenize p ≠ 0 := by
    intro h0
    have hle := hpmax q hqK
    rw [h0, abs_zero] at hle
    exact hqdet (abs_eq_zero.mp (le_antisymm hle (abs_nonneg _)))
  -- the homogenised family is a basis
  have hbasis := (Pi.basisFun ℝ (Fin (m + 1))).is_basis_iff_det.mpr (isUnit_iff_ne_zero.mpr hD)
  set B : Module.Basis (Fin (m + 1)) ℝ Vh := Module.Basis.mk hbasis.1 hbasis.2.ge with hBdef
  have hBj : ∀ j, B j = homogenize (p j) := fun j => Module.Basis.mk_apply _ _ j
  set lam : Eu → Fin (m + 1) → ℝ := fun x j => B.repr (homogenize x) j with hlamdef
  have hrepr : ∀ x : Eu, ∑ j, lam x j • homogenize (p j) = homogenize x := by
    intro x
    have h := B.sum_repr (homogenize x)
    simpa [hBj, hlamdef] using h
  have hsum1 : ∀ x : Eu, (∑ j, lam x j) = 1 := fun x => (of_homogenize_comb (hrepr x)).1
  have hcomb : ∀ x : Eu, ∑ j, lam x j • p j = x := fun x => (of_homogenize_comb (hrepr x)).2
  -- maximality bounds the barycentric coordinates of points of `K`
  have hbdd : ∀ x ∈ K.carrier, ∀ j, |lam x j| ≤ 1 := by
    intro x hx j
    have h1 : detHomogenize (Function.update p j x) = lam x j * detHomogenize p :=
      detHomogenize_update p j x (lam x) (hrepr x)
    have h2 : |detHomogenize (Function.update p j x)| ≤ |detHomogenize p| := by
      refine hpmax _ (fun k => ?_)
      by_cases h : k = j
      · subst h; rw [Function.update_self]; exact hx
      · rw [Function.update_of_ne h]; exact hpK k
    rw [h1, abs_mul] at h2
    nlinarith [abs_pos.mpr hD, h2]
  -- the coordinate functionals, and their Riesz vectors
  have hlamp : ∀ (k j : Fin (m + 1)), lam (p k) j = if j = k then 1 else 0 := by
    intro k j
    rw [hlamdef]
    simp only [← hBj k, Module.Basis.repr_self, Finsupp.single_apply]
    by_cases h : j = k
    · subst h; simp
    · rw [if_neg h, if_neg (fun hh => h hh.symm)]
  set Lin : Fin (m + 1) → (Eu →ₗ[ℝ] ℝ) :=
    fun j => (Finsupp.lapply j).comp
      ((B.repr : Vh ≃ₗ[ℝ] (Fin (m + 1) →₀ ℝ)).toLinearMap.comp homogenizeL)
    with hLindef
  have hLinapp : ∀ (j : Fin (m + 1)) (w : Eu), Lin j w = B.repr (homogenizeL w) j := fun _ _ => rfl
  have hlamdiff : ∀ (x y : Eu) (j : Fin (m + 1)), lam x j = lam y j + Lin j (x - y) := by
    intro x y j
    have hxy : homogenize x = homogenize y + homogenizeL (x - y) := by rw [← homogenize_sub]; abel
    rw [hlamdef]
    simp only [hxy, map_add, Finsupp.add_apply, hLinapp]
  have hunique : ∀ (c : Fin (m + 1) → ℝ) (x : Eu), (∑ k, c k) = 1 → (∑ k, c k • p k) = x →
      ∀ j, lam x j = c j := by
    intro c x hc1 hc2 j
    have hx : homogenize x = ∑ k, c k • B k := by
      simp only [hBj]
      exact (homogenize_comb hc1 hc2).symm
    rw [hlamdef]
    simp only [hx]
    rw [Module.Basis.repr_sum_self B c]
  exact ⟨p, lam, Lin, hpK, hsum1, hcomb, hbdd, hunique, hlamdiff⟩

private theorem exists_inner_closedBall_aux (hm : 1 ≤ m) {ϱ : ℝ} (hϱ : 0 < ϱ)
    (K : ConvexSpaceBody Eu) (hKball : K.carrier ⊆ closedBall 0 ϱ) {v : ℝ} (hv : 0 < v)
    (hvol : ENNReal.ofReal v ≤ volume K.carrier) :
    ∃ z ∈ K.carrier, closedBall z (v / (2 * (m + 1) * (2 * ϱ) ^ (m - 1))) ⊆ K.carrier := by
  classical
  have hKconv : Convex ℝ K.carrier := K.convex
  have hvolpos : 0 < volume K.carrier :=
    lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hv) hvol
  obtain ⟨p, lam, Lin, hpK, hsum1, hcomb, hbdd, hunique, hlamdiff⟩ :=
    exists_maximal_frame K hvolpos
  have hlamp : ∀ (k j : Fin (m + 1)), lam (p k) j = if j = k then 1 else 0 := by
    intro k j
    refine hunique (fun i => if i = k then 1 else 0) (p k) (by simp) (by simp) j
  obtain ⟨cvec, hcvec⟩ : ∃ cvec : Fin (m + 1) → Eu,
      ∀ (j : Fin (m + 1)) (w : Eu), Lin j w = (inner ℝ w (cvec j) : ℝ) := by
    refine ⟨fun j => (InnerProductSpace.toDual ℝ Eu).symm (LinearMap.toContinuousLinearMap (Lin j)),
      fun j w => ?_⟩
    have h : (inner ℝ ((InnerProductSpace.toDual ℝ Eu).symm
        (LinearMap.toContinuousLinearMap (Lin j))) w : ℝ) = Lin j w :=
      InnerProductSpace.toDual_symm_apply
    rw [real_inner_comm, h]
  -- each coordinate functional is nonzero
  have hcne : ∀ j, cvec j ≠ 0 := by
    intro j hj
    obtain ⟨k, hk⟩ := Fintype.exists_ne_of_one_lt_card
      (α := Fin (m + 1)) (by simpa using by omega) j
    have h1 : lam (p j) j = 1 := by rw [hlamp]; simp
    have h0 : lam (p k) j = 0 := by rw [hlamp]; simp [Ne.symm hk]
    have hd := hlamdiff (p j) (p k) j
    rw [h1, h0, hcvec, hj] at hd
    simp at hd
  -- the slab bound coming from the maximality
  have hfr : Module.finrank ℝ Eu = m := finrank_euclideanSpace_fin
  have hslab : ∀ j, ‖cvec j‖ * v ≤ 2 * (2 * ϱ)^(m-1) := by
    intro j
    have hcpos : 0 < ‖cvec j‖ := norm_pos_iff.mpr (hcne j)
    set u : Eu := ‖cvec j‖⁻¹ • cvec j with hu
    have hunorm : ‖u‖ = 1 := by
      rw [hu, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (ne_of_gt hcpos)]
    set t : ℝ := inner ℝ (p j) (cvec j) with ht
    have hIcc : ∀ x ∈ K.carrier,
        (inner ℝ x u : ℝ) ∈ Set.Icc (‖cvec j‖⁻¹ * (t - 2)) (‖cvec j‖⁻¹ * t) := by
      intro x hx
      have h1 : lam x j = 1 + (inner ℝ (x - p j) (cvec j) : ℝ) := by
        rw [hlamdiff x (p j) j, hlamp, hcvec]
        simp
      rw [inner_sub_left, ← ht] at h1
      have h2 : |lam x j| ≤ 1 := hbdd x hx j
      have h3 : (inner ℝ x (cvec j) : ℝ) = t + lam x j - 1 := by linarith
      have hinv : (0:ℝ) < ‖cvec j‖⁻¹ := inv_pos.mpr hcpos
      have h4 : (inner ℝ x u : ℝ) = ‖cvec j‖⁻¹ * (inner ℝ x (cvec j) : ℝ) := by
        rw [hu, real_inner_smul_right]
      rw [h4, h3]
      constructor
      · have := abs_le.mp h2
        nlinarith [this.1, hinv]
      · have := abs_le.mp h2
        nlinarith [this.2, hinv]
    have hvolle := volume_le_of_inner_mem_Icc_of_subset_ball hunorm hϱ.le hKball hIcc
    rw [hfr] at hvolle
    have hlen : ‖cvec j‖⁻¹ * t - ‖cvec j‖⁻¹ * (t - 2) = 2 * ‖cvec j‖⁻¹ := by ring
    rw [hlen] at hvolle
    have hchain : ENNReal.ofReal v
        ≤ ENNReal.ofReal (2 * ‖cvec j‖⁻¹ * (2 * ϱ)^(m-1)) := by
      refine hvol.trans (hvolle.trans_eq ?_)
      rw [← ENNReal.ofReal_mul (by positivity)]
    have hreal : v ≤ 2 * ‖cvec j‖⁻¹ * (2 * ϱ)^(m-1) :=
      (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hchain
    have := mul_le_mul_of_nonneg_left hreal (le_of_lt hcpos)
    calc ‖cvec j‖ * v ≤ ‖cvec j‖ * (2 * ‖cvec j‖⁻¹ * (2 * ϱ)^(m-1)) := this
      _ = 2 * (2 * ϱ)^(m-1) := by field_simp
  -- the centroid of the maximising simplex
  have hmp : (0:ℝ) < (m : ℝ)+1 := by positivity
  set wt : Fin (m + 1) → ℝ := fun _ => ((m : ℝ)+1)⁻¹ with hwt
  have hwsum : ∑ j, wt j = 1 := by
    rw [hwt]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  set z : Eu := ∑ j, wt j • p j with hzdef
  have hzK : z ∈ K.carrier :=
    hKconv.sum_mem (fun j _ => by positivity) hwsum (fun j _ => hpK j)
  have hlamz : ∀ j, lam z j = ((m : ℝ)+1)⁻¹ := fun j => hunique wt z hwsum rfl j
  -- the ball around the centroid
  set P : ℝ := (2 * ϱ)^(m-1) with hP
  have hPpos : 0 < P := by rw [hP]; positivity
  set r : ℝ := v / (2 * ((m : ℝ) + 1) * P) with hr
  have hrpos : 0 < r := by rw [hr]; positivity
  refine ⟨z, hzK, ?_⟩
  intro x hx
  have hxz : ‖x - z‖ ≤ r := by
    rw [← dist_eq_norm]
    exact mem_closedBall.mp hx
  have hnonneg : ∀ j, 0 ≤ lam x j := by
    intro j
    have h1 : lam x j = ((m : ℝ)+1)⁻¹ + (inner ℝ (x - z) (cvec j) : ℝ) := by
      rw [hlamdiff x z j, hlamz, hcvec]
    have h2 : |(inner ℝ (x - z) (cvec j) : ℝ)| ≤ ‖x - z‖ * ‖cvec j‖ :=
      abs_real_inner_le_norm _ _
    have h3 : ‖x - z‖ * ‖cvec j‖ ≤ r * ‖cvec j‖ :=
      mul_le_mul_of_nonneg_right hxz (norm_nonneg _)
    have h4 : r * ‖cvec j‖ ≤ ((m : ℝ)+1)⁻¹ := by
      rw [hr, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      have h5 : ((m : ℝ)+1)⁻¹ * (2 * ((m : ℝ) + 1) * P) = 2 * P := by
        field_simp
      rw [h5, hP]
      calc v * ‖cvec j‖ = ‖cvec j‖ * v := mul_comm _ _
        _ ≤ 2 * (2 * ϱ)^(m-1) := hslab j
    have h6 := (abs_le.mp h2).1
    linarith
  have hxeq := hcomb x
  rw [← hxeq]
  exact hKconv.sum_mem (fun j _ => hnonneg j) (hsum1 x) (fun j _ => hpK j)


/-- **Rank-one determinant.** The determinant of `w ↦ w + f w • u`. -/
private lemma det_id_add_rankOne (f : Eu →ₗ[ℝ] ℝ) (u : Eu) :
    LinearMap.det ((LinearMap.id : Eu →ₗ[ℝ] Eu) +
      (LinearMap.toSpanSingleton ℝ Eu u).comp f) = 1 + f u := by
  classical
  set b : Module.Basis (Fin m) ℝ Eu := (EuclideanSpace.basisFun (Fin m) ℝ).toBasis with hb
  rw [← LinearMap.det_toMatrix b]
  have hmat : LinearMap.toMatrix b b
      ((LinearMap.id : Eu →ₗ[ℝ] Eu) + (LinearMap.toSpanSingleton ℝ Eu u).comp f)
      = 1 + Matrix.replicateCol (Fin 1) (fun i => b.repr u i) *
          Matrix.replicateRow (Fin 1) (fun j => f (b j)) := by
    ext i j
    by_cases h : i = j
    · subst h
      simp [LinearMap.toMatrix_apply, Matrix.mul_apply,
        LinearMap.toSpanSingleton_apply, Matrix.replicateCol, Matrix.replicateRow,
        Module.Basis.repr_self, mul_comm]
    · simp [LinearMap.toMatrix_apply, Matrix.mul_apply, Matrix.replicateCol,
        Matrix.replicateRow, Module.Basis.repr_self, mul_comm, h]
  rw [hmat]
  have hlem := Matrix.det_one_add_replicateCol_mul_replicateRow (ι := Fin 1) (α := ℝ)
    (m := Fin m) (fun i => b.repr u i) (fun j => f (b j))
  refine hlem.trans ?_
  congr 1
  have hu : u = ∑ j, b.repr u j • b j := (b.sum_repr u).symm
  conv_rhs => rw [hu]
  rw [map_sum, dotProduct]
  exact Finset.sum_congr rfl fun j _ => by rw [map_smul]; simp [mul_comm]



/-- The arithmetic behind the two dilation steps: if `t ≥ -b` then the `(1 + (m + 1) b)`-fold
contraction towards the centroid of a point with barycentric coordinate `t` has nonnegative
coordinate. -/
private lemma coord_dilate_nonneg {b t : ℝ} (hb : 0 ≤ b) (ht : -b ≤ t) :
    0 ≤ ((m : ℝ)+1)⁻¹ + (1 + ((m : ℝ)+1) * b)⁻¹ * (t - ((m : ℝ)+1)⁻¹) := by
  have hm1 : (0:ℝ) < (m : ℝ)+1 := by positivity
  have ha : (0:ℝ) < 1 + ((m : ℝ)+1) * b := by positivity
  have key : ((m : ℝ)+1)⁻¹ + (1 + ((m : ℝ)+1) * b)⁻¹ * (t - ((m : ℝ)+1)⁻¹)
      = (b + t) / (1 + ((m : ℝ)+1) * b) := by
    field_simp
    ring
  rw [key]
  exact div_nonneg (by linarith) ha.le


private theorem exists_essOverlapDilate_aux {θ : ℝ} (hθ : 0 < θ) (_hθ1 : θ ≤ 1) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ M : ConvexSpaceBody Eu,
      0 < volume M.carrier → ∃ z ∈ M.carrier,
        ∀ Q : ConvexSpaceBody Eu,
          M.carrier ⊆ Q.carrier → ENNReal.ofReal θ * volume Q.carrier ≤ volume M.carrier →
          Q.carrier ⊆ AffineMap.homothety z C '' M.carrier := by
  classical
  have hm1 : (0:ℝ) < (m : ℝ) + 1 := by positivity
  have hm2 : (0:ℝ) < (m : ℝ) + 2 := by positivity
  set L0 : ℝ := ((m : ℝ)+2)^m / θ with hL0def
  have hL0 : 0 < L0 := by rw [hL0def]; positivity
  set C : ℝ := 1 + ((m : ℝ)+1) * L0 with hCdef
  have hC1 : 1 ≤ C := by rw [hCdef]; nlinarith
  have hCpos : 0 < C := by linarith
  refine ⟨C, hC1, ?_⟩
  intro M hMvolpos
  obtain ⟨p, lam, Lin, hpM, hsum1, hcomb, hbdd, hunique, hlamdiff⟩ :=
    exists_maximal_frame M hMvolpos
  have hMconv : Convex ℝ M.carrier := M.convex
  have hlamp : ∀ (k j : Fin (m + 1)), lam (p k) j = if j = k then 1 else 0 := by
    intro k j
    exact hunique (fun i => if i = k then 1 else 0) (p k) (by simp) (by simp) j
  -- the centroid of the maximal simplex
  set wt : Fin (m + 1) → ℝ := fun _ => ((m : ℝ)+1)⁻¹ with hwt
  have hwsum : ∑ j, wt j = 1 := by
    rw [hwt]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  set g : Eu := ∑ j, wt j • p j with hgdef
  have hgM : g ∈ M.carrier :=
    hMconv.sum_mem (fun j _ => by positivity) hwsum (fun j _ => hpM j)
  have hlamg : ∀ j, lam g j = ((m : ℝ)+1)⁻¹ := fun j => hunique wt g hwsum rfl j
  refine ⟨g, hgM, ?_⟩
  intro Q hMQ hvolQ
  -- the maximal simplex itself, described by its barycentric coordinates
  set D : Set Eu := {y | ∀ j, 0 ≤ lam y j} with hDdef
  have hDsub : D ⊆ M.carrier := by
    intro y hy
    rw [← hcomb y]
    exact hMconv.sum_mem (fun j _ => hy j) (hsum1 y) (fun j _ => hpM j)
  have hcont : ∀ j, Continuous fun y : Eu => lam y j := by
    intro j
    have he : (fun y : Eu => lam y j) = fun y => lam g j + Lin j (y - g) :=
      funext fun y => hlamdiff y g j
    rw [he]
    exact continuous_const.add
      ((LinearMap.continuous_of_finiteDimensional (Lin j)).comp
        (continuous_id.sub continuous_const))
  have hDpos : 0 < volume D := by
    have hopen : IsOpen {y : Eu | ∀ j, 0 < lam y j} := by
      have hEq : {y : Eu | ∀ j, 0 < lam y j} = ⋂ j, {y : Eu | 0 < lam y j} := by
        ext y; simp
      rw [hEq]
      exact isOpen_iInter_of_finite fun j => isOpen_lt continuous_const (hcont j)
    have hgmem : g ∈ {y : Eu | ∀ j, 0 < lam y j} := by
      intro j; rw [hlamg]; positivity
    exact lt_of_lt_of_le (hopen.measure_pos volume ⟨g, hgmem⟩)
      (measure_mono fun y hy j => (hy j).le)
  have hDfin : volume D ≠ ⊤ :=
    ne_top_of_le_ne_top M.isCompact.measure_ne_top (measure_mono hDsub)
  -- contracting towards the centroid, in coordinates
  have hcoordmap : ∀ a : ℝ, a ≠ 0 → ∀ (x : Eu) (j : Fin (m + 1)),
      lam (g + a⁻¹ • (x - g)) j = ((m : ℝ)+1)⁻¹ + a⁻¹ * (lam x j - ((m : ℝ)+1)⁻¹) := by
    intro a ha x j
    rw [hlamdiff (g + a⁻¹ • (x - g)) g j, hlamg]
    congr 1
    have hgg : g + a⁻¹ • (x - g) - g = a⁻¹ • (x - g) := by abel
    rw [hgg, map_smul, smul_eq_mul]
    congr 1
    have h2 := hlamdiff x g j
    rw [hlamg] at h2
    linarith
  have hhom : ∀ a : ℝ, a ≠ 0 → ∀ x : Eu,
      AffineMap.homothety g a (g + a⁻¹ • (x - g)) = x := by
    intro a ha x
    have hgg : g + a⁻¹ • (x - g) - g = a⁻¹ • (x - g) := by abel
    simp [AffineMap.homothety_apply, hgg, smul_smul, mul_inv_cancel₀ ha]
  -- `M` lies in the `(m + 2)`-dilate of the simplex about its centroid
  have hm2eq : (1 : ℝ) + ((m : ℝ)+1) * 1 = (m : ℝ) + 2 := by ring
  have hMdil : M.carrier ⊆ AffineMap.homothety g ((m : ℝ)+2) '' D := by
    intro x hx
    refine ⟨g + ((m : ℝ)+2)⁻¹ • (x - g), fun j => ?_, hhom _ (ne_of_gt hm2) x⟩
    rw [hcoordmap _ (ne_of_gt hm2) x j, ← hm2eq]
    exact coord_dilate_nonneg zero_le_one (neg_le_of_abs_le (hbdd x hx j))
  have hMvol : volume M.carrier ≤ ENNReal.ofReal (((m : ℝ)+2)^m) * volume D := by
    refine (measure_mono hMdil).trans ?_
    rw [Measure.addHaar_image_homothety]
    have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) = m := finrank_euclideanSpace_fin
    rw [hfr, abs_of_nonneg (by positivity : (0:ℝ) ≤ ((m : ℝ)+2)^m)]
  -- maximality of the simplex bounds the barycentric coordinates of `Q` from below
  have hQcoord : ∀ x ∈ Q.carrier, ∀ j, -L0 ≤ lam x j := by
    intro x hx j0
    by_contra hcon
    push Not at hcon
    have hLpos : 0 < -(lam x j0) := by
      have : (0:ℝ) < L0 := hL0
      linarith
    set u : Eu := x - p j0 with hudef
    set A : Eu →ₗ[ℝ] Eu :=
      LinearMap.id + (LinearMap.toSpanSingleton ℝ Eu u).comp (Lin j0) with hAdef
    have hLinx : Lin j0 u = lam x j0 - 1 := by
      have h := hlamdiff x (p j0) j0
      rw [hlamp j0 j0, if_pos rfl] at h
      rw [hudef]
      linarith
    have hdetA : LinearMap.det A = lam x j0 := by
      rw [hAdef, det_id_add_rankOne, hLinx]
      ring
    set Tf : Eu → Eu := fun y => y + (lam y j0) • u with hTfdef
    have hTfaff : ∀ y : Eu, Tf y = A y + (lam 0 j0) • u := by
      intro y
      have hy := hlamdiff y 0 j0
      simp only [sub_zero] at hy
      rw [hTfdef, hAdef]
      simp only [LinearMap.add_apply, LinearMap.id_apply, LinearMap.comp_apply,
        LinearMap.toSpanSingleton_apply]
      rw [hy, add_smul, add_assoc, add_comm (lam 0 j0 • u)]
    have hTfsum : ∀ y : Eu, Tf y = ∑ j, lam y j • (Function.update p j0 x) j := by
      intro y
      have hterm : ∀ j : Fin (m + 1), lam y j • (Function.update p j0 x) j
          = lam y j • p j + (if j = j0 then lam y j0 • u else 0) := by
        intro j
        by_cases h : j = j0
        · subst h
          rw [Function.update_self, if_pos rfl, hudef, smul_sub]
          abel
        · rw [Function.update_of_ne h, if_neg h, add_zero]
      rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_add_distrib,
        Finset.sum_ite_eq' Finset.univ j0 (fun _ => lam y j0 • u), hcomb y,
        if_pos (Finset.mem_univ _)]
    have hTfQ : Tf '' D ⊆ Q.carrier := by
      rintro _ ⟨y, hy, rfl⟩
      rw [hTfsum y]
      refine Q.convex.sum_mem (fun j _ => hy j) (hsum1 y) (fun j _ => ?_)
      by_cases h : j = j0
      · rw [h, Function.update_self]; exact hx
      · rw [Function.update_of_ne h]; exact hMQ (hpM j)
    have hvolTf : volume (Tf '' D) = ENNReal.ofReal (-(lam x j0)) * volume D := by
      have himg : Tf '' D = (fun w : Eu => w + (lam 0 j0) • u) '' (A '' D) := by
        rw [← Set.image_comp]
        exact Set.image_congr' (fun y => hTfaff y)
      rw [himg, Set.image_add_right, measure_preimage_add_right,
        Measure.addHaar_image_linearMap, hdetA, abs_of_neg (by linarith : lam x j0 < 0)]
    have hchain : ENNReal.ofReal (θ * -(lam x j0)) * volume D
        ≤ ENNReal.ofReal (((m : ℝ)+2)^m) * volume D := by
      calc ENNReal.ofReal (θ * -(lam x j0)) * volume D
          = ENNReal.ofReal θ * (ENNReal.ofReal (-(lam x j0)) * volume D) := by
            rw [ENNReal.ofReal_mul hθ.le, mul_assoc]
        _ = ENNReal.ofReal θ * volume (Tf '' D) := by rw [hvolTf]
        _ ≤ ENNReal.ofReal θ * volume Q.carrier := by
            gcongr
        _ ≤ volume M.carrier := hvolQ
        _ ≤ _ := hMvol
    have hcancel : ENNReal.ofReal (θ * -(lam x j0)) ≤ ENNReal.ofReal (((m : ℝ)+2)^m) :=
      (ENNReal.mul_le_mul_iff_left (ne_of_gt hDpos) hDfin).mp hchain
    have hreal : θ * -(lam x j0) ≤ ((m : ℝ)+2)^m :=
      (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hcancel
    have hlt : L0 < -(lam x j0) := by linarith
    rw [hL0def] at hlt
    have hlt2 := (div_lt_iff₀ hθ).mp hlt
    nlinarith [hlt2, hreal]
  -- conclusion
  intro x hx
  refine ⟨g + C⁻¹ • (x - g), hDsub (fun j => ?_), hhom C (ne_of_gt hCpos) x⟩
  rw [hcoordmap C (ne_of_gt hCpos) x j, hCdef]
  exact coord_dilate_nonneg hL0.le (hQcoord x hx j)


end InnerBallSimplex

/-- **A convex body of large volume contains a ball** (blueprint `lem:convexInnerBallVolume`).

The displayed radius uses the constant `2 (n + 1)`. It is *not* obtained from Steinhagen's
inequality — which Mathlib does not have, along with the inradius and the minimal width — but
from the elementary maximal-simplex argument of
`Kakeya.exists_inner_closedBall_aux`, which happens to give exactly this constant: maximality of
the simplex volume confines `K` to a slab of half-width `h_j` about each facet hyperplane, so
`h_j ≥ v / (2 (2ϱ)^{n-1})`, and the centroid is at distance `h_j / (n+1)` from that hyperplane.
Only the existence of some positive radius depending on `n`, `v` and `ϱ` alone is used
downstream. -/
theorem exists_closedBall_subset_of_le_volume (hm : 1 ≤ m) {ϱ : ℝ} (hϱ : 0 < ϱ)
    (K : ConvexSpaceBody (EuclideanSpace ℝ (Fin m)))
    (hKball : K.carrier ⊆ closedBall 0 ϱ) {v : ℝ} (hv : 0 < v)
    (hvol : ENNReal.ofReal v ≤ volume K.carrier) :
    ∃ z ∈ K.carrier, closedBall z (v / (2 * (m + 1) * (2 * ϱ) ^ (m - 1))) ⊆ K.carrier :=
  exists_inner_closedBall_aux hm hϱ K hKball hv hvol

/-- **Shrinking a set into a convex body it almost lies in** (blueprint
`lem:convexHomothetSubsetOfNbhd`).

If `K` is convex and contains the ball `B̄(z, ρ)`, and `L` lies in the `ε`-neighbourhood of
`K`, then the homothet of `L` about `z` of ratio `1 - σ`, with `σ = ε / (ρ + ε)`, lies in `K`.

This is the convex-body form of the private helper `homothety_subset_inter` of
`Kakeya/Tube/CardEssentiallyDistinct.lean`, with the inner ball `B̄(z, ρ)` playing the role
that the segment endpoints play for a tube. -/
theorem convex_homothety_image_subset (K : ConvexSpaceBody (EuclideanSpace ℝ (Fin m)))
    {L : Set (EuclideanSpace ℝ (Fin m))}
    {z : EuclideanSpace ℝ (Fin m)} {ρ : ℝ} (hρ : 0 < ρ) (hball : closedBall z ρ ⊆ K.carrier)
    {ε : ℝ} (hε : 0 ≤ ε) (hL : L ⊆ K.carrier + closedBall (0 : EuclideanSpace ℝ (Fin m)) ε) :
    AffineMap.homothety z (1 - ε / (ρ + ε)) '' L ⊆ K.carrier := by
  rintro p ⟨y, hyL, rfl⟩
  rcases hL hyL with ⟨k, hk, e, he, hke⟩
  have hρe : 0 < ρ + ε := by linarith
  by_cases hε0 : ε = 0
  · -- ε = 0 : the homothety is the identity and the enlargement collapses to K
    have he0 : e = 0 := by
      have he' : dist e (0 : EuclideanSpace ℝ (Fin m)) ≤ 0 := by
        rw [hε0] at he
        exact Metric.mem_closedBall.mp he
      exact dist_eq_zero.mp (le_antisymm he' dist_nonneg)
    have hr : 1 - ε / (ρ + ε) = (1 : ℝ) := by
      rw [hε0]
      simp
    rw [hr]
    simp only [AffineMap.homothety_one]
    rw [← hke, he0]
    simpa using hk
  · have hεpos : 0 < ε := lt_of_le_of_ne hε (Ne.symm hε0)
    let σ : ℝ := ε / (ρ + ε)
    have hσ0 : 0 ≤ σ := by
      unfold σ
      exact div_nonneg hε (le_of_lt hρe)
    have hσ1 : σ ≤ 1 := by
      unfold σ
      rw [← div_self (ne_of_gt hρe)]
      exact div_le_div_of_nonneg_right (by linarith) (le_of_lt hρe)
    let c : ℝ := ρ / ε
    have hcpos : 0 < c := by
      unfold c
      exact div_pos hρ hεpos
    have hc_eq : ρ = c * ε := by
      unfold c
      field_simp [hεpos.ne']
    have hw : z + c • e ∈ K.carrier := by
      apply hball
      rw [Metric.mem_closedBall]
      have hn : ‖e‖ ≤ ε := by
        have hde := Metric.mem_closedBall.mp he
        simpa [dist_eq_norm] using hde
      calc
        dist (z + c • e) z = ‖c • e‖ := by simp [dist_eq_norm]
        _ = c * ‖e‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hcpos)]
        _ ≤ ρ := by
          rw [hc_eq]
          nlinarith [hn, le_of_lt hcpos]
    have hσc : σ * c = 1 - σ := by
      unfold σ c
      field_simp [hεpos.ne', hρe.ne']
      ring
    have hp : AffineMap.homothety z (1 - ε / (ρ + ε)) y = k + σ • (z + c • e - k) := by
      have hr : (1 - ε / (ρ + ε) : ℝ) = 1 - σ := by rfl
      rw [hr, ← hke, AffineMap.homothety_apply]
      conv_rhs =>
        rw [smul_sub, smul_add]
        rw [smul_smul σ c e, hσc]
      simp only [vadd_eq_add, vsub_eq_sub]
      module
    rw [hp]
    exact Convex.add_smul_sub_mem K.convex hk hw ⟨hσ0, hσ1⟩

/-- **An inner ball survives an `ε`-enlargement** (blueprint `lem:innerBallOfNbhd`).

If the ball `B̄(z, ρ)` lies in the `ε`-neighbourhood of a nonempty compact convex `L`, then the
shrunken ball `B̄(z, ρ - ε)` lies in `L` itself.

Convexity of `L` is essential and not a convenience: it is what makes strict separation of a
point from `L` available, and the conclusion is false for a non-convex `L` already for two
far-apart points. -/
theorem closedBall_subset_of_closedBall_subset_add (L : ConvexSpaceBody (EuclideanSpace ℝ (Fin m)))
    {z : EuclideanSpace ℝ (Fin m)} {ρ ε : ℝ} (hε : 0 ≤ ε) (hερ : ε ≤ ρ)
    (h : closedBall z ρ ⊆ L.carrier + closedBall (0 : EuclideanSpace ℝ (Fin m)) ε) :
    closedBall z (ρ - ε) ⊆ L.carrier := by
  intro x hx
  by_contra hnot
  let E := EuclideanSpace ℝ (Fin m)
  have hρ0 : 0 ≤ ρ := le_trans hε hερ
  -- strict separation of x from the closed convex body L.carrier
  rcases geometric_hahn_banach_closed_point (s := L.carrier) L.convex L.isCompact.isClosed hnot with
    ⟨f, c, hisoL, hcx⟩
  -- f = inner w, i.e. f = toDual w
  rcases (InnerProductSpace.toDual ℝ E).surjective f with ⟨w, hwf⟩
  have htoDual : ∀ y : E, ⟪w, y⟫ = f y := by
    intro y
    rw [← hwf, InnerProductSpace.toDual_apply_apply]
  rcases L.nonempty with ⟨a0, ha0⟩
  have hwa : ∀ a ∈ L.carrier, ⟪w, a⟫ < c := by
    intro a ha
    rw [htoDual a]
    exact hisoL a ha
  have hcxw : c < ⟪w, x⟫ := by
    rw [htoDual x]
    exact hcx
  have hw_ne : w ≠ 0 := by
    intro hw0
    have hlt : ⟪w, a0⟫ < ⟪w, x⟫ := lt_trans (hwa a0 ha0) hcxw
    simp [hw0] at hlt
  have hnpos : 0 < ‖w‖ := norm_pos_iff.mpr hw_ne
  -- unit vector u in the separating direction
  let u : E := (‖w‖⁻¹) • w
  have hnorm : ‖u‖ = 1 := by
    dsimp [u]
    rw [norm_smul]
    rw [Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg w))]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw_ne)
  let t : ℝ := c / ‖w‖
  have hu_left : ∀ y : E, ⟪y, u⟫ = ‖w‖⁻¹ * ⟪y, w⟫ := by
    intro y
    simp [u, real_inner_smul_right]
  have hLu : ∀ a ∈ L.carrier, ⟪a, u⟫ < t := by
    intro a ha
    dsimp [t]
    rw [hu_left a, real_inner_comm]
    have hmul : ‖w‖⁻¹ * ⟪w, a⟫ < ‖w‖⁻¹ * c :=
      mul_lt_mul_of_pos_left (hwa a ha) (inv_pos.mpr hnpos)
    simpa [div_eq_mul_inv, mul_comm] using hmul
  have hxu_t : t < ⟪x, u⟫ := by
    dsimp [t]
    rw [hu_left x, real_inner_comm]
    have hmul : ‖w‖⁻¹ * c < ‖w‖⁻¹ * ⟪w, x⟫ :=
      mul_lt_mul_of_pos_left hcxw (inv_pos.mpr hnpos)
    simpa [div_eq_mul_inv, mul_comm] using hmul
  -- the pushed point p = z + ρ u
  let p : E := z + ρ • u
  have hp : p ∈ closedBall z ρ := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hsub : p - z = ρ • u := by
      dsimp [p]
      abel
    rw [hsub, norm_smul, hnorm, Real.norm_of_nonneg hρ0]
    norm_num
  rcases h hp with ⟨q, hq, e, he, hpe⟩
  have he_norm : ‖e‖ ≤ ε := by
    simpa [dist_eq_norm] using (mem_closedBall.mp he)
  have hxz : ‖x - z‖ ≤ ρ - ε := by
    simpa [dist_eq_norm] using (mem_closedBall.mp hx)
  have he_le : ⟪e, u⟫ ≤ ε := by
    calc
      ⟪e, u⟫ ≤ ‖e‖ * ‖u‖ := real_inner_le_norm _ _
      _ = ‖e‖ := by rw [hnorm, mul_one]
      _ ≤ ε := he_norm
  have hpuc : ⟪p, u⟫ < t + ε := by
    have hp_in : ⟪p, u⟫ = ⟪q, u⟫ + ⟪e, u⟫ := by
      rw [← hpe, inner_add_left]
    rw [hp_in]
    exact add_lt_add_of_lt_of_le (hLu q hq) he_le
  have hp_eq : ⟪p, u⟫ = ⟪z, u⟫ + ρ := by
    dsimp [p]
    rw [inner_add_left, real_inner_smul_left]
    simp [hnorm]
  have hpz : ⟪z, u⟫ + ρ < t + ε := by
    rwa [hp_eq] at hpuc
  have hz_lt : ⟪z, u⟫ < t + ε - ρ := by linarith [hpz]
  have hx_le : ⟪x, u⟫ ≤ ⟪z, u⟫ + (ρ - ε) := by
    calc
      ⟪x, u⟫ = ⟪z, u⟫ + ⟪x - z, u⟫ := by
        rw [← inner_add_left]
        congr 1
        abel
      _ ≤ ⟪z, u⟫ + ‖x - z‖ * ‖u‖ := by
        rw [add_le_add_iff_left]
        exact real_inner_le_norm (x - z) u
      _ = ⟪z, u⟫ + ‖x - z‖ := by rw [hnorm, mul_one]
      _ ≤ ⟪z, u⟫ + (ρ - ε) := by
        rw [add_le_add_iff_left]
        exact hxz
  have hx_lt_t : ⟪x, u⟫ < t := by
    have hmid : ⟪z, u⟫ + (ρ - ε) < t := by
      linarith [hz_lt]
    exact lt_of_le_of_lt hx_le hmid
  exact (not_lt_of_ge (le_of_lt hx_lt_t)) hxu_t

/-- **A shrunken homothet lands in both bodies** (blueprint `lem:convexHomothetSubsetInter`,
containment half).

The containment in `K` is `Kakeya.convex_homothety_image_subset`; the containment in `L` holds
because `z + (1 - σ)(y - z)` is a convex combination of `y ∈ L` and `z ∈ L`. -/
theorem convex_homothety_image_subset_inter
    (K L : ConvexSpaceBody (EuclideanSpace ℝ (Fin m)))
    {z : EuclideanSpace ℝ (Fin m)} (hzL : z ∈ L.carrier)
    {ρ : ℝ} (hρ : 0 < ρ) (hball : closedBall z ρ ⊆ K.carrier)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hLK : L.carrier ⊆ K.carrier + closedBall (0 : EuclideanSpace ℝ (Fin m)) ε) :
    AffineMap.homothety z (1 - ε / (ρ + ε)) '' L.carrier ⊆ K.carrier ∩ L.carrier := by
  rw [Set.subset_inter_iff]
  constructor
  · exact convex_homothety_image_subset K hρ hball hε hLK
  · intro x hx
    rcases hx with ⟨y, hyL, rfl⟩
    set c : ℝ := 1 - ε / (ρ + ε) with hc
    have hρadd : 0 < ρ + ε := add_pos_of_pos_of_nonneg hρ hε
    have hεdiv : 0 ≤ ε / (ρ + ε) := div_nonneg hε (le_of_lt hρadd)
    have hεdiv1 : ε / (ρ + ε) ≤ 1 := (div_le_one hρadd).mpr (by linarith)
    have hc0 : 0 ≤ c := by rw [hc]; linarith
    have h1c : 0 ≤ 1 - c := by rw [hc]; linarith
    have hsum : c + (1 - c) = 1 := by ring
    have hlin : c • (y - z) + z = c • y + (1 - c) • z := by module
    rw [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, hlin,
      ← convexCombPair_eq_smul_add hc0 h1c hsum y z]
    exact L.convex'.convexCombPair_mem hyL hzL hc0 h1c hsum

/-- **A shrunken homothet lands in both bodies** (blueprint `lem:convexHomothetSubsetInter`,
volume half).

Monotonicity along `Kakeya.convex_homothety_image_subset_inter`, together with the homothety
volume formula. -/
theorem volume_inter_ge_of_homothety
    (K L : ConvexSpaceBody (EuclideanSpace ℝ (Fin m)))
    {z : EuclideanSpace ℝ (Fin m)} (hzL : z ∈ L.carrier)
    {ρ : ℝ} (hρ : 0 < ρ) (hball : closedBall z ρ ⊆ K.carrier)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hLK : L.carrier ⊆ K.carrier + closedBall (0 : EuclideanSpace ℝ (Fin m)) ε) :
    ENNReal.ofReal ((1 - ε / (ρ + ε)) ^ m) * volume L.carrier
      ≤ volume (K.carrier ∩ L.carrier) := by
  have hρadd : 0 < ρ + ε := add_pos_of_pos_of_nonneg hρ hε
  have hεdiv1 : ε / (ρ + ε) ≤ 1 := (div_le_one hρadd).mpr (by linarith)
  have hnonneg : (0 : ℝ) ≤ 1 - ε / (ρ + ε) := by linarith
  have hsubset := convex_homothety_image_subset_inter K L hzL hρ hball hε hLK
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) = m := finrank_euclideanSpace_fin
  have hvol : volume (AffineMap.homothety z (1 - ε / (ρ + ε)) '' L.carrier)
      = ENNReal.ofReal (|((1 - ε / (ρ + ε)) ^
          Module.finrank ℝ (EuclideanSpace ℝ (Fin m)))|) * volume L.carrier :=
    MeasureTheory.Measure.addHaar_image_homothety
      (μ := (volume : Measure (EuclideanSpace ℝ (Fin m)))) z (1 - ε / (ρ + ε)) L.carrier
  rw [hfr, abs_of_nonneg (pow_nonneg hnonneg m)] at hvol
  calc ENNReal.ofReal ((1 - ε / (ρ + ε)) ^ m) * volume L.carrier
      = volume (AffineMap.homothety z (1 - ε / (ρ + ε)) '' L.carrier) := hvol.symm
    _ ≤ volume (K.carrier ∩ L.carrier) := measure_mono hsubset

/-- **Two Hausdorff-close convex bodies overlap in a fixed fraction** (blueprint
`lem:essOverlapVolumeLower`).

If `K` contains a ball of radius `ρ`, and `K` and `L` are `ε`-close in the Hausdorff sense with
`ε < ρ`, then `|K ∩ L| ≥ (1 - ε/ρ)ⁿ max(|K|, |L|)`.

The strict inequality `ε < ρ` is spent on the second of the two applications of
`Kakeya.convex_homothety_image_subset_inter`, the one at the *shrunken* ball
`B̄(z, ρ - ε) ⊆ L`. -/
theorem volume_inter_ge_of_hausdorff_close (K L : ConvexSpaceBody (EuclideanSpace ℝ (Fin m)))
    {z : EuclideanSpace ℝ (Fin m)} {ρ : ℝ} (hρ : 0 < ρ) (hball : closedBall z ρ ⊆ K.carrier)
    {ε : ℝ} (hε : 0 ≤ ε) (hερ : ε < ρ)
    (hKL : K.carrier ⊆ L.carrier + closedBall (0 : EuclideanSpace ℝ (Fin m)) ε)
    (hLK : L.carrier ⊆ K.carrier + closedBall (0 : EuclideanSpace ℝ (Fin m)) ε) :
    ENNReal.ofReal ((1 - ε / ρ) ^ m) * max (volume K.carrier) (volume L.carrier)
      ≤ volume (K.carrier ∩ L.carrier) := by
  have hρadd : 0 < ρ + ε := by linarith
  have hρε : 0 < ρ - ε := by linarith
  have hdivlt : ε / ρ < 1 := (div_lt_one hρ).mpr hερ
  have hbase : (0 : ℝ) ≤ 1 - ε / ρ := by linarith
  -- the inner ball of `K` shrinks to an inner ball of `L`
  have hballL : closedBall z (ρ - ε) ⊆ L.carrier :=
    closedBall_subset_of_closedBall_subset_add L hε (by linarith)
      (hball.trans hKL)
  have hzL : z ∈ L.carrier := hballL (Metric.mem_closedBall_self hρε.le)
  have hzK : z ∈ K.carrier := hball (Metric.mem_closedBall_self hρ.le)
  -- (a) the bound carrying `volume L.carrier`
  have hA : ENNReal.ofReal ((1 - ε / ρ) ^ m) * volume L.carrier
      ≤ volume (K.carrier ∩ L.carrier) := by
    have h1 := volume_inter_ge_of_homothety K L hzL hρ hball hε hLK
    refine le_trans (mul_le_mul_right' ?_ _) h1
    refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hbase ?_ m)
    have hmono : ε / (ρ + ε) ≤ ε / ρ := by gcongr; linarith
    linarith
  -- (b) the bound carrying `volume K.carrier`
  have hB : ENNReal.ofReal ((1 - ε / ρ) ^ m) * volume K.carrier
      ≤ volume (K.carrier ∩ L.carrier) := by
    have h2 := volume_inter_ge_of_homothety L K hzK hρε hballL hε hKL
    rw [sub_add_cancel] at h2
    rw [Set.inter_comm]
    exact h2
  rcases le_total (volume K.carrier) (volume L.carrier) with h | h
  · rw [max_eq_right h]; exact hA
  · rw [max_eq_left h]; exact hB

/-- **Essentially distinct convex bodies are Hausdorff-separated** (blueprint
`lem:essDistinctSeparationRadius`).

In the situation of `Kakeya.volume_inter_ge_of_hausdorff_close`, essential distinctness of `K`
and `L` forces `ε ≥ (1 - 2^{-1/n}) ρ`: the factor `max(|K|, |L|)` is positive, being at least
the volume of the inner ball, and finite, so it cancels and leaves `(1 - ε/ρ)ⁿ ≤ 1/2`. -/
theorem hausdorff_separated_of_essDistinct (hm : 1 ≤ m)
    (K L : ConvexSpaceBody (EuclideanSpace ℝ (Fin m)))
    {z : EuclideanSpace ℝ (Fin m)} {ρ : ℝ} (hρ : 0 < ρ) (hball : closedBall z ρ ⊆ K.carrier)
    {ε : ℝ} (hε : 0 ≤ ε) (hερ : ε < ρ)
    (hKL : K.carrier ⊆ L.carrier + closedBall (0 : EuclideanSpace ℝ (Fin m)) ε)
    (hLK : L.carrier ⊆ K.carrier + closedBall (0 : EuclideanSpace ℝ (Fin m)) ε)
    (hed : IsEssentiallyDistinct K.carrier L.carrier) :
    (1 - (2 : ℝ) ^ (-(1 : ℝ) / m)) * ρ ≤ ε := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hdivlt : ε / ρ < 1 := (div_lt_one hρ).mpr hερ
  have hbase : (0 : ℝ) ≤ 1 - ε / ρ := by linarith
  set M : ENNReal := max (volume K.carrier) (volume L.carrier) with hM
  have hKpos : 0 < volume K.carrier :=
    lt_of_lt_of_le (measure_closedBall_pos volume z hρ) (measure_mono hball)
  have hM0 : M ≠ 0 := by
    rw [hM]
    exact ne_of_gt (lt_of_lt_of_le hKpos (le_max_left _ _))
  have hMtop : M ≠ ⊤ := by
    rw [hM, ← lt_top_iff_ne_top]
    exact max_lt (lt_top_iff_ne_top.mpr K.isCompact.measure_ne_top)
      (lt_top_iff_ne_top.mpr L.isCompact.measure_ne_top)
  have hlow := volume_inter_ge_of_hausdorff_close K L hρ hball hε hερ hKL hLK
  have hchain : ENNReal.ofReal ((1 - ε / ρ) ^ m) * M ≤ (1 / 2 : ENNReal) * M :=
    le_trans hlow hed
  have hhalf : ENNReal.ofReal ((1 - ε / ρ) ^ m) ≤ (1 / 2 : ENNReal) :=
    (ENNReal.mul_le_mul_iff_left hM0 hMtop).mp hchain
  have hhalfR : (1 / 2 : ENNReal) = ENNReal.ofReal (1 / 2 : ℝ) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  rw [hhalfR] at hhalf
  have hreal : (1 - ε / ρ) ^ m ≤ (1 / 2 : ℝ) :=
    (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp hhalf
  -- compare with the `m`-th power of `2 ^ (-1/m)`
  set b : ℝ := (2 : ℝ) ^ (-(1 : ℝ) / m) with hb
  have hbpos : 0 < b := Real.rpow_pos_of_pos (by norm_num) _
  have hbm : b ^ m = (1 / 2 : ℝ) := by
    rw [hb, ← Real.rpow_natCast ((2 : ℝ) ^ (-(1 : ℝ) / m)) m,
      ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    rw [div_mul_cancel₀ _ hm0]
    rw [Real.rpow_neg_one]
    norm_num
  have hle : (1 - ε / ρ) ≤ b := by
    have := hreal
    rw [← hbm] at this
    exact (pow_le_pow_iff_left₀ hbase hbpos.le (by omega)).mp this
  have : (1 - b) ≤ ε / ρ := by linarith
  exact (le_div_iff₀ hρ).mp this

/-- **A Hausdorff-separated family in a bounded set is finite** (blueprint
`lem:cardHausdorffSeparated`), in the only form in which it is true: the cover pieces are
controlled by the *pointwise* distance bound `dist x y ≤ ε` rather than by
`Metric.diam (cover i) ≤ ε`.

The distinction is not cosmetic. `Metric.diam` of an *unbounded* set is `0` by convention, so a
hypothesis phrased with `Metric.diam` carries no information about an unbounded cover piece,
and the trace argument below genuinely needs two points of one piece to be `ε`-close. -/
private theorem card_le_of_pairwise_not_close_of_cover {ε : ℝ}
    {A : Set (EuclideanSpace ℝ (Fin m))} {N : ℕ} (cover : Fin N → Set (EuclideanSpace ℝ (Fin m)))
    (hcover : A ⊆ ⋃ i, cover i)
    (hdist : ∀ i, ∀ x ∈ cover i, ∀ y ∈ cover i, dist x y ≤ ε)
    {ι : Type*} (s : Finset ι) (K : ι → Set (EuclideanSpace ℝ (Fin m)))
    (hKA : ∀ j ∈ s, K j ⊆ A)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ¬(K i ⊆ K j + closedBall (0 : EuclideanSpace ℝ (Fin m)) ε ∧
        K j ⊆ K i + closedBall (0 : EuclideanSpace ℝ (Fin m)) ε)) :
    #s ≤ 2 ^ N := by
  classical
  set tr : ι → Finset (Fin N) := fun j => {c ∈ Finset.univ | (K j ∩ cover c).Nonempty} with htr
  -- equal traces force mutual `ε`-closeness
  have hclose : ∀ i ∈ s, ∀ j ∈ s, tr i = tr j →
      K i ⊆ K j + closedBall (0 : EuclideanSpace ℝ (Fin m)) ε := by
    intro i hi j hj heq x hx
    obtain ⟨c, hc⟩ := Set.mem_iUnion.mp (hcover (hKA i hi hx))
    have hci : c ∈ tr i := by
      rw [htr]; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨x, hx, hc⟩
    rw [heq, htr] at hci
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hci
    obtain ⟨y, hyK, hyc⟩ := hci
    have hd : dist x y ≤ ε := hdist c x hc y hyc
    refine ⟨y, hyK, x - y, ?_, by abel⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    rwa [dist_eq_norm] at hd
  have hinj : Set.InjOn tr (s : Set ι) := by
    intro i hi j hj heq
    by_contra hij
    exact hsep i hi j hj hij
      ⟨hclose i hi j hj heq, hclose j hj i hi heq.symm⟩
  calc #s ≤ #(Finset.univ : Finset (Finset (Fin N))) :=
        Finset.card_le_card_of_injOn tr (fun a _ => Finset.mem_univ _) hinj
    _ = 2 ^ N := by simp [Finset.card_univ, Fintype.card_finset]


/-!
## `Kakeya.card_le_of_pairwise_not_hausdorff_close` is no longer stated here

It asserted
that a family of pairwise not-mutually-`ε`-close subsets of a set `A` covered by `N` pieces
`cover i` with `Metric.diam (cover i) ≤ ε` has at most `2 ^ N` members. It has been **deleted**,
because the statement was false as written.

In Mathlib `Metric.diam` is `ENNReal.toReal ∘ EMetric.diam`, so an *unbounded* set has
`Metric.diam = 0`. Hence `∀ i, Metric.diam (cover i) ≤ ε` is satisfied by a cover consisting of
unbounded pieces, the covering hypothesis carries no information whatsoever, and the conclusion
fails: take `N = 1`, `cover 0 = Set.univ`, `A = Set.univ` and an arbitrarily large family of
pairwise `2ε`-separated singletons, all of which satisfy every hypothesis while `#s` is
unbounded.

The repaired statement is `Kakeya.card_le_of_pairwise_not_close_of_cover` immediately above,
which replaces the vacuous diameter hypothesis by the pointwise bound
`∀ i, ∀ x ∈ cover i, ∀ y ∈ cover i, dist x y ≤ ε` (equivalent to the diameter bound exactly for
*bounded* pieces) and drops the then-unused `hε` and `hKne`. It is proved, and it is what
`Kakeya.card_le_of_pairwise_essDistinct_in_prism` consumes, together with the matching cover
producer `Kakeya.exists_cover_dist_le`.
-/

/-- **A ball is a union of boundedly many small sets** (blueprint `lem:ballCoverByDiameterEps`),
in the form the counting argument consumes: the grid cover it builds
satisfies the *pointwise* distance bound `dist x y ≤ ε` on each piece, not merely
`Metric.diam ≤ ε`. The two are equivalent only for bounded pieces, and the pointwise form is
what the counting argument consumes. -/
private theorem exists_cover_dist_le (hm : 1 ≤ m) {ϱ ε : ℝ} (hϱ : 0 < ϱ) (hε : 0 < ε) :
    ∃ (N : ℕ) (cover : Fin N → Set (EuclideanSpace ℝ (Fin m))),
      (N : ℝ) ≤ (2 + 2 * ϱ * Real.sqrt m / ε) ^ m ∧
      closedBall (0 : EuclideanSpace ℝ (Fin m)) ϱ ⊆ ⋃ i, cover i ∧
      ∀ i, ∀ x ∈ cover i, ∀ y ∈ cover i, dist x y ≤ ε := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.mpr hmR
  set s : ℝ := ε / Real.sqrt m with hs
  have hspos : 0 < s := div_pos hε hsm
  set k : ℕ := ⌈2 * ϱ / s⌉₊ + 1 with hk
  have hkpos : 0 < k := Nat.succ_pos _
  -- the grid cube attached to a multi-index
  let cube : (Fin m → Fin k) → Set (EuclideanSpace ℝ (Fin m)) := fun a =>
    {x | ∀ i, -ϱ + (a i : ℝ) * s ≤ x i ∧ x i ≤ -ϱ + ((a i : ℝ) + 1) * s}
  refine ⟨k ^ m, fun j => cube (finFunctionFinEquiv.symm j), ?_, ?_, ?_⟩
  · -- cardinality bound
    have h2ϱ : (0 : ℝ) ≤ 2 * ϱ / s := le_of_lt (div_pos (by linarith) hspos)
    have hceil : (⌈2 * ϱ / s⌉₊ : ℝ) ≤ 2 * ϱ / s + 1 :=
      le_of_lt (Nat.ceil_lt_add_one h2ϱ)
    have hsr : 2 * ϱ / s = 2 * ϱ * Real.sqrt m / ε := by
      rw [hs]; field_simp
    have hkR0 : (k : ℝ) ≤ 2 * ϱ / s + 2 := by
      rw [hk]; push_cast; linarith
    rw [hsr] at hkR0
    have hkR : (k : ℝ) ≤ 2 + 2 * ϱ * Real.sqrt m / ε := by linarith
    calc ((k ^ m : ℕ) : ℝ) = (k : ℝ) ^ m := by push_cast; ring
      _ ≤ (2 + 2 * ϱ * Real.sqrt m / ε) ^ m :=
          pow_le_pow_left₀ (by positivity) hkR m
  · -- covering
    intro x hx
    have hxi : ∀ i : Fin m, |x i| ≤ ϱ := by
      intro i
      have h1 : ‖x i‖ ≤ ‖x‖ := PiLp.norm_apply_le x i
      have h2 : ‖x‖ ≤ ϱ := by simpa [dist_eq_norm] using Metric.mem_closedBall.mp hx
      simpa [Real.norm_eq_abs] using h1.trans h2
    have hidx : ∀ i : Fin m, ⌊(x i + ϱ) / s⌋₊ < k := by
      intro i
      have h0 : 0 ≤ (x i + ϱ) / s := by
        have := (abs_le.mp (hxi i)).1
        exact div_nonneg (by linarith) hspos.le
      have hub : (x i + ϱ) / s ≤ 2 * ϱ / s := by
        have := (abs_le.mp (hxi i)).2
        gcongr
        linarith
      have : ⌊(x i + ϱ) / s⌋₊ ≤ ⌈2 * ϱ / s⌉₊ :=
        le_trans (Nat.floor_le_ceil _) (Nat.ceil_le_ceil hub)
      omega
    let a : Fin m → Fin k := fun i => ⟨⌊(x i + ϱ) / s⌋₊, hidx i⟩
    refine Set.mem_iUnion.mpr ⟨finFunctionFinEquiv a, ?_⟩
    rw [Equiv.symm_apply_apply]
    intro i
    have hfl : ((a i : ℕ) : ℝ) ≤ (x i + ϱ) / s := Nat.floor_le (by
      have := (abs_le.mp (hxi i)).1
      exact div_nonneg (by linarith) hspos.le)
    have hfu : (x i + ϱ) / s < ((a i : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
    constructor
    · have h := (le_div_iff₀ hspos).mp hfl
      linarith
    · have h := (div_lt_iff₀ hspos).mp hfu
      linarith
  · -- pairwise distance
    intro j x hx y hy
    set a := finFunctionFinEquiv.symm j with ha
    have hcomp : ∀ i, |x i - y i| ≤ s := by
      intro i
      have hx' := hx i
      have hy' := hy i
      rw [abs_le]
      constructor <;> [linarith [hx'.1, hy'.2]; linarith [hx'.2, hy'.1]]
    rw [EuclideanSpace.dist_eq]
    have hsum : ∑ i, dist (x i) (y i) ^ 2 ≤ (m : ℝ) * s ^ 2 := by
      calc ∑ i : Fin m, dist (x i) (y i) ^ 2 ≤ ∑ _i : Fin m, s ^ 2 := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [Real.dist_eq]
            exact pow_le_pow_left₀ (abs_nonneg _) (hcomp i) 2
        _ = (m : ℝ) * s ^ 2 := by simp [Finset.sum_const]
    calc Real.sqrt (∑ i, dist (x i) (y i) ^ 2) ≤ Real.sqrt ((m : ℝ) * s ^ 2) :=
          Real.sqrt_le_sqrt hsum
      _ = ε := by
          rw [Real.sqrt_mul hmR.le, Real.sqrt_sq hspos.le, hs]
          field_simp


/-- **A ball is a union of boundedly many sets of small diameter** (blueprint
`lem:ballCoverByDiameterEps`).

The cover is by half-open grid cubes of side `ε / √n`, intersected with the ball.

The discretization machinery already in the development does not supply this:
`Kakeya.exists_finite_test_family_maxDensity_closedBall` covers a ball by prisms adapted to a
family of convex bodies and controls their *number* but not their *diameter*.

This is the blueprint's own phrasing, kept for reference; it is *not* what the counting argument
consumes. A `Metric.diam` bound says nothing about an unbounded piece, so the counting argument
uses the pointwise form `Kakeya.exists_cover_dist_le` instead — see the note below on the
deleted `Kakeya.card_le_of_pairwise_not_hausdorff_close`. -/
theorem exists_cover_diam_le (hm : 1 ≤ m) {ϱ ε : ℝ} (hϱ : 0 < ϱ) (hε : 0 < ε) :
    ∃ (N : ℕ) (cover : Fin N → Set (EuclideanSpace ℝ (Fin m))),
      (N : ℝ) ≤ (2 + 2 * ϱ * Real.sqrt m / ε) ^ m ∧
      closedBall (0 : EuclideanSpace ℝ (Fin m)) ϱ ⊆ ⋃ i, cover i ∧
      ∀ i, Metric.diam (cover i) ≤ ε := by
  obtain ⟨N, cover, hN, hcov, hdist⟩ := exists_cover_dist_le hm hϱ hε
  exact ⟨N, cover, hN, hcov, fun i => Metric.diam_le_of_forall_dist_le hε.le (hdist i)⟩

/-- **Constant in Lemma `lem:cardEssDistinctConvexInPrism`** (blueprint
`def:cardEssDistinctConvexInPrismConstant`, `D_{lem:cardEssDistinctConvexInPrism}(n, α)`).

Reading the displayed expression from the inside out, it is `2 ^ N(n, α)` where, in order,

* `ρ(n, α) = α 2ⁿ / (2 (n+1) (2 √n)^{n-1})` is the inner radius that
  `Kakeya.exists_closedBall_subset_of_le_volume` returns at `ϱ = √n` and `v = α 2ⁿ`;
* `ε(n, α) = ½ (1 - 2^{-1/n}) ρ(n, α)` is a separation strictly below the threshold of
  `Kakeya.hausdorff_separated_of_essDistinct`;
* `N(n, α) = ⌈(2 + 2n/ε(n, α))ⁿ⌉` is the cover size that `Kakeya.exists_cover_dist_le` returns
  at `ϱ = √n` and that separation.

It **must** be allowed to depend on `α`, and no bound uniform in `α` exists: as `α → 0`,
arbitrarily many pairwise essentially distinct convex bodies of volume at least `α |R|` fit
inside a fixed prism `R` — for instance `α⁻¹` pairwise disjoint parallel slices of it. The
value is enormous and deliberately crude; nothing downstream uses anything but its finiteness
and its argument list. -/
def cardEssDistinctConvexInPrismConstant (m : ℕ) (α : ℝ) : ℕ :=
  2 ^ ⌈(2 + 2 * m / ((1 - (2 : ℝ) ^ (-(1 : ℝ) / m)) / 2 *
    (α * 2 ^ m / (2 * (m + 1) * (2 * Real.sqrt m) ^ (m - 1))))) ^ m⌉₊

/-- **Counting essentially distinct convex bodies of large volume in a prism** (blueprint
`lem:cardEssDistinctConvexInPrism`).

Both hypotheses earn their place. The comparability `|K j| ≥ α |R|` is the right one, and the
constant must depend on `α`, for the reason recorded with
`Kakeya.cardEssDistinctConvexInPrismConstant`. And `|R| > 0` cannot be dropped: if `|R| = 0`
then every `K j ⊆ R` has `|K j| = 0`, the volume hypothesis is vacuous, and every pair is
essentially distinct, so the cardinality is unbounded. -/
theorem card_le_of_pairwise_essDistinct_in_prism (hm : 1 ≤ m) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (R : PrismNDim m (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin m)))
    (hR : 0 < volume (R.carrier : Set (EuclideanSpace ℝ (Fin m))))
    {ι : Type*} (s : Finset ι) (K : ι → ConvexSpaceBody (EuclideanSpace ℝ (Fin m)))
    (hKR : ∀ j ∈ s, (K j).carrier ⊆ (R.carrier : Set (EuclideanSpace ℝ (Fin m))))
    (hKvol : ∀ j ∈ s, ENNReal.ofReal α * volume (R.carrier : Set (EuclideanSpace ℝ (Fin m)))
      ≤ volume (K j).carrier)
    (hed : (s : Set ι).Pairwise fun i j => IsEssentiallyDistinct (K i).carrier (K j).carrier) :
    #s ≤ cardEssDistinctConvexInPrismConstant m α := by
  classical
  set E := EuclideanSpace ℝ (Fin m)
  obtain ⟨T, hTimg, hTvol⟩ := R.exists_affineEquiv_image_eq_cube hR
  set Cb : PrismNDim m E E := PrismNDim.mk' (0 : E) R.basis (fun _ => (1 : NNReal)) with hCb
  set K' : ι → ConvexSpaceBody E := fun j => (K j).mapAffine T with hK'
  have hK'carrier : ∀ j, (K' j).carrier = T '' (K j).carrier := fun j => rfl
  have hRne0 : volume (R.carrier : Set E) ≠ 0 := hR.ne'
  have hRnetop : volume (R.carrier : Set E) ≠ ⊤ := R.isCompact.measure_ne_top
  -- basic positivity of the numerical parameters
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  set ϱ : ℝ := Real.sqrt m with hϱdef
  have hϱ : 0 < ϱ := Real.sqrt_pos.mpr hmR
  set v : ℝ := α * 2 ^ m with hvdef
  have hv : 0 < v := by positivity
  set ρ : ℝ := v / (2 * ((m : ℝ) + 1) * (2 * ϱ) ^ (m - 1)) with hρdef
  have hden : (0 : ℝ) < 2 * ((m : ℝ) + 1) * (2 * ϱ) ^ (m - 1) := by positivity
  have hρ : 0 < ρ := div_pos hv hden
  set η : ℝ := 1 - (2 : ℝ) ^ (-(1 : ℝ) / m) with hηdef
  have hpow1 : (2 : ℝ) ^ (-(1 : ℝ) / m) < 1 := by
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    exact div_neg_of_neg_of_pos (by norm_num) hmR
  have hpow0 : (0 : ℝ) < (2 : ℝ) ^ (-(1 : ℝ) / m) := Real.rpow_pos_of_pos (by norm_num) _
  have hη0 : 0 < η := by rw [hηdef]; linarith
  have hη1 : η ≤ 1 := by rw [hηdef]; linarith
  set ε : ℝ := η / 2 * ρ with hεdef
  have hε : 0 < ε := by positivity
  have hερ : ε < ρ := by
    rw [hεdef]
    nlinarith [hρ, hη0, hη1]
  -- the transported bodies live in the unit cube, hence in the ball of radius `√m`
  have hcube : (Cb.carrier : Set E) ⊆ closedBall (0 : E) ϱ := by
    have h := Cb.carrier_subset_closedBall_euclidean
    have hc : Cb.center = (0 : E) := by rw [hCb, PrismNDim.center_mk']
    have ht : ∀ i, (Cb.thicknesses i : ℝ) = 1 := by
      intro i; rw [hCb, PrismNDim.thicknesses_mk']; norm_num
    have hsum : Real.sqrt (∑ i, (Cb.thicknesses i : ℝ) ^ 2) = ϱ := by
      rw [hϱdef]
      congr 1
      simp [ht]
    rwa [hc, hsum] at h
  have hK'sub : ∀ j ∈ s, (K' j).carrier ⊆ closedBall (0 : E) ϱ := by
    intro j hj
    rw [hK'carrier]
    refine subset_trans ?_ hcube
    rw [← hTimg]
    exact Set.image_mono (hKR j hj)
  -- the transported bodies have volume at least `α 2 ^ m`
  have hK'vol : ∀ j ∈ s, ENNReal.ofReal v ≤ volume (K' j).carrier := by
    intro j hj
    have h1 : volume (R.carrier : Set E) * volume (T '' (K j).carrier)
        = 2 ^ m * volume (K j).carrier := hTvol _
    have h2 : (2 : ENNReal) ^ m * (ENNReal.ofReal α * volume (R.carrier : Set E))
        ≤ 2 ^ m * volume (K j).carrier := by
      exact mul_le_mul_left' (hKvol j hj) _
    have h3 : ((2 : ENNReal) ^ m * ENNReal.ofReal α) * volume (R.carrier : Set E)
        ≤ volume (T '' (K j).carrier) * volume (R.carrier : Set E) := by
      rw [mul_comm (volume (T '' (K j).carrier))]
      calc ((2 : ENNReal) ^ m * ENNReal.ofReal α) * volume (R.carrier : Set E)
          = 2 ^ m * (ENNReal.ofReal α * volume (R.carrier : Set E)) := by ring
        _ ≤ 2 ^ m * volume (K j).carrier := h2
        _ = volume (R.carrier : Set E) * volume (T '' (K j).carrier) := h1.symm
    have h4 : (2 : ENNReal) ^ m * ENNReal.ofReal α ≤ volume (T '' (K j).carrier) :=
      (ENNReal.mul_le_mul_iff_left hRne0 hRnetop).mp h3
    have h5 : ENNReal.ofReal v = (2 : ENNReal) ^ m * ENNReal.ofReal α := by
      rw [hvdef, ENNReal.ofReal_mul hα.le, ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 2)]
      rw [ENNReal.ofReal_ofNat]
      ring
    rw [hK'carrier, h5]
    exact h4
  -- inner balls
  have hballs : ∀ j ∈ s, ∃ z ∈ (K' j).carrier, closedBall z ρ ⊆ (K' j).carrier := by
    intro j hj
    exact exists_closedBall_subset_of_le_volume hm hϱ (K' j) (hK'sub j hj) hv (hK'vol j hj)
  -- essential distinctness transports
  have hed' : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      IsEssentiallyDistinct (K' i).carrier (K' j).carrier := by
    intro i hi j hj hij
    rw [hK'carrier, hK'carrier]
    exact IsEssentiallyDistinct.image_affineEquiv T (hed hi hj hij)
  -- the transported bodies are pairwise `ε`-separated
  have hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ¬((K' i).carrier ⊆ (K' j).carrier + closedBall (0 : E) ε ∧
        (K' j).carrier ⊆ (K' i).carrier + closedBall (0 : E) ε) := by
    intro i hi j hj hij hcon
    obtain ⟨z, _, hz⟩ := hballs i hi
    have hkey := hausdorff_separated_of_essDistinct hm (K' i) (K' j) hρ hz hε.le hερ
      hcon.1 hcon.2 (hed' i hi j hj hij)
    rw [← hηdef] at hkey
    rw [hεdef] at hkey
    nlinarith [hρ, hη0]
  -- the grid cover of the ball of radius `√m`
  obtain ⟨N, cover, hN, hcov, hdist⟩ := exists_cover_dist_le hm hϱ hε
  have hcard : #s ≤ 2 ^ N :=
    card_le_of_pairwise_not_close_of_cover cover hcov hdist s (fun j => (K' j).carrier)
      hK'sub hsep
  refine le_trans hcard ?_
  rw [cardEssDistinctConvexInPrismConstant]
  refine Nat.pow_le_pow_right (by norm_num) ?_
  have hεexpand : (1 - (2 : ℝ) ^ (-(1 : ℝ) / m)) / 2 *
      (α * 2 ^ m / (2 * ((m : ℝ) + 1) * (2 * Real.sqrt m) ^ (m - 1))) = ε := by
    rw [hεdef, hηdef, hρdef, hvdef, hϱdef]
  rw [hεexpand]
  have hϱϱ : 2 * ϱ * Real.sqrt m / ε = 2 * (m : ℝ) / ε := by
    rw [hϱdef, mul_assoc, Real.mul_self_sqrt hmR.le]
  rw [hϱϱ] at hN
  have : (N : ℝ) ≤ (2 + 2 * (m : ℝ) / ε) ^ m := hN
  have hceil : (N : ℝ) ≤ (⌈(2 + 2 * (m : ℝ) / ε) ^ m⌉₊ : ℝ) :=
    le_trans this (Nat.le_ceil _)
  exact_mod_cast hceil

/-- **A body of comparable volume controls its container up to a dilate** (blueprint
`lem:essOverlapDilate`).

The intended argument took `z_M` to be the centroid of `M` and combined Grünbaum's centroid
inequality with Brunn's theorem, neither of which Mathlib has (nor the centroid of a convex
body). The proof used here avoids all three: `z_M` is the centroid of the *maximal-volume
inscribed simplex* of `M` (the private `exists_maximal_frame` of this file), which is
elementary and, being
affinely equivariant, loses nothing on flat bodies. Maximality gives the two inclusions that do
all the work, both read off in barycentric coordinates:

* `M` lies in the `(m+2)`-dilate of that simplex `Δ` about `z_M`, so `|M| ≤ (m+2)^m |Δ|`;
* if some `x ∈ Q` had barycentric coordinate `-L` then replacing the corresponding vertex by `x`
  gives a simplex inside `Q` of volume `L |Δ|` — the determinant ratio is `L` by the rank-one
  determinant identity — so `θ L |Δ| ≤ θ |Q| ≤ |M| ≤ (m+2)^m |Δ|` and `L ≤ (m+2)^m / θ`.

Hence `C = 1 + (m+1)(m+2)^m/θ` works. The constant is enormous and deliberately crude, and the
hypothesis `θ ≤ 1` is not needed for it (it is kept because the blueprint states it).

Note that the witness `z_M` is quantified **before** `Q` and depends on `M` alone. That
ordering is exactly what `Kakeya.VeryNotSticky.exists_isClusterDilationConstant` consumes —
it applies the statement to the single body `M = P ∩ Q` and to the two containers `P` and `Q`
in turn, and needs the *same* centre for both — and a version quantifying `z` after `Q` would
not serve. -/
theorem exists_essOverlapDilate_constant (m : ℕ) {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ M : ConvexSpaceBody (EuclideanSpace ℝ (Fin m)),
      0 < volume M.carrier → ∃ z ∈ M.carrier,
        ∀ Q : ConvexSpaceBody (EuclideanSpace ℝ (Fin m)),
          M.carrier ⊆ Q.carrier → ENNReal.ofReal θ * volume Q.carrier ≤ volume M.carrier →
          Q.carrier ⊆ AffineMap.homothety z C '' M.carrier :=
  exists_essOverlapDilate_aux hθ hθ1

end Kakeya

end

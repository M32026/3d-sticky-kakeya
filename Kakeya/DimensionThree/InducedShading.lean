/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.CShading
public import Kakeya.FactorFamily.Predicates
public import Kakeya.ConvexBody
public import Kakeya.Projection
public import Kakeya.DimensionTwo.CordobaAffine
public import Kakeya.Thickness.Attained
public import Kakeya.Thickness.ConvexSpaceBody
public import Kakeya.Thickening

/-! # Density of the induced shading in three dimensions

The `ℝ³`-specific density lower bounds for induced shadings: GWZ Lemma 5.9
(`lambdaForInducedShading`) and its single-body forms (`lambdaInducedSingleW` and the
uniform-shading special case `lambdaInducedSingleWUniform`). These estimates are special to
`ℝ³` (hypothesis `hdim`), since their proofs use the planar Cordoba estimate and the projection
lemmas of `Kakeya.Projection`.

The dimension-general multiplicity statements about induced shadings remain in
`Kakeya.Multiplicity`. -/

@[expose] public section
open MeasureTheory Convexity EuclideanGeometry
open scoped Kakeya.AffineSubspaceArea

namespace ShadedBody

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι κ : Type*}
  (s : Finset ι) (V : ι → ShadedBody E)

/-- The convex-thickening volume-doubling constant `Θ(n, m) = 2ⁿmⁿ / c_n`, where
`c_n = Metric.lt_volume_convexHull.c n = (n!)⁻¹` is the inscribed-simplex constant: if `a ≤ m·b`
then `|N_a(X)| ≤ Θ(n,m)·|N_b(X)|` for every nonempty convex `X` (blueprint
`def:constCthickeningDoubling`). -/
noncomputable def cthickeningDoublingConst (n m : ℕ) : NNReal :=
  2 ^ n * (m : NNReal) ^ n / Metric.lt_volume_convexHull.c n

/-- The convex-thickening doubling constant is positive for a positive dilation factor. -/
theorem cthickeningDoublingConst_pos (n : ℕ) {m : ℕ} (hm : 0 < m) :
    0 < cthickeningDoublingConst n m := by
  rw [cthickeningDoublingConst]
  have hc := Metric.lt_volume_convexHull.c_pos n
  positivity

/-- The projection volume-comparison constant `D` (blueprint eq:projectionVolumeComparison): for a
body already thickened at scale `2r` and living in the slab `N_{3r}(H)`, the shadow obeys
`6r·|π(V)| ≤ D·|V|`. Its value is the four-fold doubling constant in dimension three, because the
bound is obtained from `|π⁻¹(πV) ∩ N_{3r}(H)| ≤ |N_{6r}(V)|` together with `8r ≤ 4·(2r)`. -/
noncomputable def projectionVolumeComparisonConst : NNReal := cthickeningDoublingConst 3 4

/-- The projection-volume comparison loss is positive. -/
theorem projectionVolumeComparisonConst_pos : 0 < projectionVolumeComparisonConst := by
  exact cthickeningDoublingConst_pos 3 (by norm_num)

/-- The thickening volume-ratio constant `M(n) = 2^{4n}/c_n²` (blueprint
`def:constThickeningRatio`): under pairwise comparable affine thicknesses,
`|N_t(V_i)|·|V_j| ≤ M(n)·|N_t(V_j)|·|V_i|`, so the thickening ratio `|N_t(V_i)|/|V_i|` is uniform
over the family up to `M(n)`. -/
noncomputable def thickeningRatioConst (n : ℕ) : NNReal :=
  2 ^ (4 * n) / Metric.lt_volume_convexHull.c n ^ 2

/-- The thickening-ratio loss is positive. -/
theorem thickeningRatioConst_pos (n : ℕ) : 0 < thickeningRatioConst n := by
  rw [thickeningRatioConst]
  have hc := Metric.lt_volume_convexHull.c_pos n
  positivity

/-- Loss for changing the aggregate density weights from the original three-dimensional
carriers to their two-dimensional projected carriers. -/
noncomputable def aggregateProjectionWeightConst : NNReal :=
  Metric.volume_comparison.C 3 * Metric.volume_comparison.C 2

/-- The aggregate projection-weight comparison loss is positive. -/
theorem aggregateProjectionWeightConst_pos : 0 < aggregateProjectionWeightConst := by
  rw [aggregateProjectionWeightConst]
  exact mul_pos (Metric.volume_comparison.C_pos 3) (Metric.volume_comparison.C_pos 2)

/-- The product-body volume-ratio constant `κ` (blueprint `def:constProductBodyRatio`): the slab
product body over the shadow of `N_{2r}(K)` has volume at most `κ·|K|`, since it is contained in
`N_{8r}(K)` and `r` is the shortest affine thickness of `K` (so `8r + τ_k ≤ 9τ_k`). -/
noncomputable def productBodyVolumeRatioConst : NNReal := cthickeningDoublingConst 3 9

/-- The product-body volume-ratio loss is positive. -/
theorem productBodyVolumeRatioConst_pos : 0 < productBodyVolumeRatioConst := by
  exact cthickeningDoublingConst_pos 3 (by norm_num)

/-- Absolute constant in the uniform single-body induced-shading density lower bound
`lambdaInducedSingleWUniform`, worked out in blueprint `def:constLemma59`:
`C₅․₉ = 68 · c₂⁻¹ · c_th⁻² · D⁵ · (1 + M²) · κ · R²`, where
`c₂ = le_volume_biUnion_TwoDim.c` is the planar
Cordoba constant, `c_th = volume_cthickening_ge_of_volume_ge.c 3` is the joint-thickening shading
constant, `D = projectionVolumeComparisonConst`, `M = thickeningRatioConst 3` and
`κ = productBodyVolumeRatioConst`, while `R = aggregateProjectionWeightConst` is the
aggregate projection-weight comparison loss. -/
noncomputable def lambdaInducedSingleWUniform.C : NNReal :=
  68 * (ConvexSpaceBody.IsFrostmanIn.le_volume_biUnion_TwoDim.c)⁻¹
    * (IsConvexSet.volume_cthickening_ge_of_volume_ge.c 3)⁻¹ ^ 2
    * projectionVolumeComparisonConst ^ 5
    * (1 + thickeningRatioConst 3 ^ 2)
    * productBodyVolumeRatioConst
    * aggregateProjectionWeightConst ^ 2

/-- The uniform aggregate Córdoba loss is strictly positive. -/
theorem lambdaInducedSingleWUniform.C_pos : 0 < lambdaInducedSingleWUniform.C := by
  have hc₂ := ConvexSpaceBody.IsFrostmanIn.le_volume_biUnion_TwoDim.c_pos
  have hcth := IsConvexSet.volume_cthickening_ge_of_volume_ge.c_pos 3
  have hproj := projectionVolumeComparisonConst_pos
  have hratio := thickeningRatioConst_pos 3
  have hprod := productBodyVolumeRatioConst_pos
  have hagg := aggregateProjectionWeightConst_pos
  rw [lambdaInducedSingleWUniform.C]
  positivity

/-- The scale-dependent constant in GWZ Lemma 5.9. The factor `N + 1` records the allowed
logarithmic dependence on the eccentricity range, and the factor `4` compensates for retaining
only bodies whose shading proportion is at least half the aggregate fullness. -/
noncomputable def lambdaForInducedShading.C (N : ℕ) : NNReal :=
  4 * lambdaInducedSingleWUniform.C * (N + 1)

/-- The `ℝ≥0∞` form of `lambdaInducedSingleWUniform.C`, matching the shape produced by
`assemble_bound`. -/
private lemma coe_lambdaInducedSingleWUniform_C :
    (lambdaInducedSingleWUniform.C : ENNReal)
      = 68 * (ConvexSpaceBody.IsFrostmanIn.le_volume_biUnion_TwoDim.c : ENNReal)⁻¹
        * ((IsConvexSet.volume_cthickening_ge_of_volume_ge.c 3 : ENNReal))⁻¹ ^ 2
        * (projectionVolumeComparisonConst : ENNReal) ^ 5
        * (1 + (thickeningRatioConst 3 : ENNReal) ^ 2)
        * (productBodyVolumeRatioConst : ENNReal)
        * (aggregateProjectionWeightConst : ENNReal) ^ 2 := by
  have hc₂ : ConvexSpaceBody.IsFrostmanIn.le_volume_biUnion_TwoDim.c ≠ 0 :=
    (ConvexSpaceBody.IsFrostmanIn.le_volume_biUnion_TwoDim.c_pos).ne'
  have hcth : IsConvexSet.volume_cthickening_ge_of_volume_ge.c 3 ≠ 0 :=
    (IsConvexSet.volume_cthickening_ge_of_volume_ge.c_pos 3).ne'
  simp only [lambdaInducedSingleWUniform.C, ENNReal.coe_min, ENNReal.coe_one, ENNReal.coe_mul,
    ENNReal.coe_add, one_div,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, ENNReal.coe_inv, ENNReal.coe_pow,
    ENNReal.coe_ofNat, hc₂, hcth, aggregateProjectionWeightConst]

/-- The `ℝ≥0∞` form of the scale-dependent constant `lambdaForInducedShading.C`. -/
private lemma coe_lambdaForInducedShading_C (N : ℕ) :
    (lambdaForInducedShading.C N : ENNReal) =
      4 * (lambdaInducedSingleWUniform.C : ENNReal) * ((N : ENNReal) + 1) := by
  simp [lambdaForInducedShading.C]

/-- Transfer an aggregate density bound between two systems of comparable weights.

The hypothesis is written in cross-multiplied form: `a i * b j ≤ R * b i * a j` says that the
ratios `b i / a i` are pairwise comparable by `R`, without introducing division.  Consequently
the `a`-weighted and `b`-weighted averages of any nonnegative function differ by at most `R`.
This is the algebraic bridge used to pass from three-dimensional carrier weights to the projected
two-dimensional carrier weights in the aggregate form of Lemma 5.9. -/
theorem weightedAverage_transfer_of_cross_comparable {I : Type*} (s : Finset I)
    (a b q : I → ENNReal) (lam R : ENNReal)
    (hA0 : (∑ i ∈ s, a i) ≠ 0) (hAtop : (∑ i ∈ s, a i) ≠ ⊤)
    (hcross : ∀ i ∈ s, ∀ j ∈ s, a i * b j ≤ R * b i * a j)
    (havg : lam * (∑ i ∈ s, a i) ≤ ∑ i ∈ s, q i * a i) :
    lam * (∑ i ∈ s, b i) ≤ R * (∑ i ∈ s, q i * b i) := by
  classical
  apply (ENNReal.mul_le_mul_iff_right hA0 hAtop).mp
  calc
    (∑ i ∈ s, a i) * (lam * ∑ i ∈ s, b i) =
        (lam * ∑ i ∈ s, a i) * (∑ i ∈ s, b i) := by ring
    _ ≤ (∑ i ∈ s, q i * a i) * (∑ i ∈ s, b i) := by gcongr
    _ = ∑ i ∈ s, ∑ j ∈ s, q i * (a i * b j) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ ∑ i ∈ s, ∑ j ∈ s, q i * (R * b i * a j) := by
      exact Finset.sum_le_sum fun i hi ↦ Finset.sum_le_sum fun j hj ↦ by
        simpa [mul_assoc, mul_comm, mul_left_comm] using
          mul_le_mul_left (hcross i hi j hj) (q i)
    _ = ∑ i ∈ s, (q i * (R * b i)) * (∑ j ∈ s, a j) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = (∑ i ∈ s, q i * (R * b i)) * (∑ j ∈ s, a j) := by
      rw [Finset.sum_mul]
    _ = (∑ i ∈ s, a i) * (R * ∑ i ∈ s, q i * b i) := by
      have hsum : (∑ i ∈ s, q i * (R * b i)) = R * ∑ i ∈ s, q i * b i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hsum]
      ring

/-- Orthogonal projection of a shaded body onto an affine subspace `A`, assuming its shade is
closed. Since the shade is a closed subset of the compact carrier it is compact, so its image
under `orthogonalProjection A` is compact, hence closed, hence measurable; thus the projected
carrier and shade form a genuine `ShadedBody` on `↑A`. -/
noncomputable def orthogonalProjectionImage (S : ShadedBody E) (A : AffineSubspace ℝ E)
    [Nonempty ↑A] (hclosed : IsClosed S.shade) : ShadedBody ↑A where
  toConvexSpaceBody := S.toConvexSpaceBody.orthogonalProjectionImage A
  shade := orthogonalProjection A '' S.shade
  measurableSet_shade := by
    -- S.shade is closed (hclosed) and subset of S.carrier (S.shade_subset); S.carrier is compact
    have h_compact_shade : IsCompact S.shade :=
      S.isCompact'.of_isClosed_subset hclosed S.shade_subset
    -- orthogonalProjection A is continuous
    have h_cont : Continuous (orthogonalProjection A) :=
      (orthogonalProjection A).cont
    -- image under continuous map of compact set is compact
    have h_compact_image : IsCompact (orthogonalProjection A '' S.shade) :=
      h_compact_shade.image h_cont
    -- in a T2 space, compact implies closed
    have h_closed_image : IsClosed (orthogonalProjection A '' S.shade) :=
      h_compact_image.isClosed
    -- closed implies measurable (Borel space)
    exact h_closed_image.measurableSet
  shade_subset := by
    -- S.shade ⊆ S.carrier, so the image under orthogonalProjection A is contained in
    -- the image of S.carrier, which is exactly the carrier of the projected convex space body
    calc
      orthogonalProjection A '' S.shade
          ⊆ orthogonalProjection A '' S.carrier := Set.image_mono S.shade_subset
      _ = ((S.toConvexSpaceBody.orthogonalProjectionImage A : ConvexSpaceBody ↑A) : Set ↑A) := by
        simp

/-- **Projection of a closed shading** (blueprint `def:cshadedBodyOrthogonalProjectionImage`):
the orthogonal projection onto a nonempty affine subspace `A` of a closed shaded body, with
carrier the shadow of the carrier and shade the shadow of the shade.

Unlike `ShadedBody.orthogonalProjectionImage`, which takes closedness of the shade as a side
hypothesis and returns a body whose shade carries no closedness proof, this is a total function
`CShadedBody E → CShadedBody ↑A`, so it composes. The shade of the image is closed because the
shade of a `CShadedBody` is compact (`CShadedBody.isCompact_shade`) and `orthogonalProjection A`
is continuous. -/
noncomputable def _root_.CShadedBody.orthogonalProjectionImage (S : CShadedBody E)
    (A : AffineSubspace ℝ E) [Nonempty ↑A] : CShadedBody ↑A where
  toConvexSpaceBody := S.toConvexSpaceBody.orthogonalProjectionImage A
  shade := orthogonalProjection A '' S.shade
  isClosed_shade := by
    exact (S.isCompact_shade.image (orthogonalProjection A).cont).isClosed
  shade_subset := by
    calc
      orthogonalProjection A '' S.shade ⊆ orthogonalProjection A '' S.carrier :=
        Set.image_mono S.shade_subset
      _ = ((S.toConvexSpaceBody.orthogonalProjectionImage A : ConvexSpaceBody ↑A) : Set ↑A) := by
        simp

/-! ### Volume comparison helpers for convex thickenings

The three lemmas below are the quantitative volume inputs of the single-body reduction. They are
dimension-general; only their instantiations use `hdim`. -/

omit [Nontrivial E] in
private lemma coe_cthickeningDoublingConst (n m : ℕ) :
    (cthickeningDoublingConst n m : ENNReal)
      = 2 ^ n * (m : ENNReal) ^ n * (Metric.lt_volume_convexHull.c n : ENNReal)⁻¹ := by
  rw [cthickeningDoublingConst]
  rw [ENNReal.coe_div (Metric.lt_volume_convexHull.c_pos n).ne']
  rw [div_eq_mul_inv]
  norm_cast

/-- **Volume doubling for convex thickenings at two radii** (blueprint
`lem:cthickeningDoubling`): if `a ≤ m·b` then `|N_a(X)| ≤ Θ(n,m)·|N_b(X)|`. Both sides are
comparable to `∏_k (radius + τ_k(X))`, and `a + τ_k ≤ m·(b + τ_k)`. -/
private lemma volume_cthickening_le_doubling_mul {X : Set E} (hX : Convex ℝ X) (hXne : X.Nonempty)
    {m : ℕ} (hm : 1 ≤ m) {a b : NNReal} (hab : a ≤ m * b) :
    volume (Metric.cthickening (a : ℝ) X)
      ≤ (cthickeningDoublingConst (Module.finrank ℝ E) m : ENNReal) *
        volume (Metric.cthickening (b : ℝ) X) := by
  rw [coe_cthickeningDoublingConst]
  have hc0 : (Metric.lt_volume_convexHull.c (Module.finrank ℝ E) : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr (Metric.lt_volume_convexHull.c_pos (Module.finrank ℝ E)).ne'
  have hctop : (Metric.lt_volume_convexHull.c (Module.finrank ℝ E) : ENNReal) ≠ ⊤ :=
    ENNReal.coe_ne_top
  have hpointwise : ∀ k ∈ Finset.range (Module.finrank ℝ E),
      (a : ENNReal) + Metric.ethickness ℝ X k
        ≤ (m : ENNReal) * ((b : ENNReal) + Metric.ethickness ℝ X k) := by
    intro k hk
    have hle : (a : ENNReal) ≤ (m : ENNReal) * (b : ENNReal) := by
      exact_mod_cast hab
    have hm' : (1 : ENNReal) ≤ (m : ENNReal) := by
      exact_mod_cast hm
    have hτ : Metric.ethickness ℝ X k ≤ (m : ENNReal) * Metric.ethickness ℝ X k := by
      calc
        Metric.ethickness ℝ X k = (1 : ENNReal) * Metric.ethickness ℝ X k := by simp
        _ ≤ (m : ENNReal) * Metric.ethickness ℝ X k :=
          mul_le_mul_left hm' (Metric.ethickness ℝ X k)
    calc
      (a : ENNReal) + Metric.ethickness ℝ X k
          ≤ (m : ENNReal) * (b : ENNReal) + Metric.ethickness ℝ X k := by
            gcongr
      _ ≤ (m : ENNReal) * (b : ENNReal) + (m : ENNReal) * Metric.ethickness ℝ X k := by
            gcongr
      _ = (m : ENNReal) * ((b : ENNReal) + Metric.ethickness ℝ X k) := by
            rw [← mul_add]
  have hprod_b_le : (∏ k ∈ Finset.range (Module.finrank ℝ E),
        ((b : ENNReal) + Metric.ethickness ℝ X k))
      ≤ (Metric.lt_volume_convexHull.c (Module.finrank ℝ E) : ENNReal)⁻¹ *
        volume (Metric.cthickening (b : ℝ) X) := by
    rw [← ENNReal.div_eq_inv_mul]
    rw [ENNReal.le_div_iff_mul_le (Or.inl hc0) (Or.inl hctop)]
    simpa [mul_comm] using prod_add_le_volume_cthickening hX hXne b
  calc
    volume (Metric.cthickening (a : ℝ) X)
        ≤ 2 ^ Module.finrank ℝ E *
            ∏ k ∈ Finset.range (Module.finrank ℝ E),
              ((a : ENNReal) + Metric.ethickness ℝ X k) := by
          exact volume_cthickening_le_prod_add X a
    _ ≤ 2 ^ Module.finrank ℝ E *
          ∏ k ∈ Finset.range (Module.finrank ℝ E),
            ((m : ENNReal) * ((b : ENNReal) + Metric.ethickness ℝ X k)) := by
          gcongr with k hk
          exact hpointwise k hk
    _ = 2 ^ Module.finrank ℝ E * (m : ENNReal) ^ Module.finrank ℝ E *
          ∏ k ∈ Finset.range (Module.finrank ℝ E), ((b : ENNReal) + Metric.ethickness ℝ X k) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
          ring
    _ ≤ 2 ^ Module.finrank ℝ E * (m : ENNReal) ^ Module.finrank ℝ E *
          ((Metric.lt_volume_convexHull.c (Module.finrank ℝ E) : ENNReal)⁻¹ *
            volume (Metric.cthickening (b : ℝ) X)) := by
          gcongr
    _ = (2 ^ Module.finrank ℝ E * (m : ENNReal) ^ Module.finrank ℝ E *
          (Metric.lt_volume_convexHull.c (Module.finrank ℝ E) : ENNReal)⁻¹) *
          volume (Metric.cthickening (b : ℝ) X) := by
          ring

/-- **Volume of a thickening against the body itself** (blueprint `lem:cthickeningVsBody`): if
`a + τ_k(X) ≤ m·τ_k(X)` at every rank `k` below the ambient dimension, then
`|N_a(X)| ≤ Θ(n,m)·|X|`. -/
private lemma volume_cthickening_le_doubling_mul_volume {X : Set E} (hX : Convex ℝ X)
    {m : ℕ} {a : NNReal}
    (ha : ∀ k ∈ Finset.range (Module.finrank ℝ E),
      (a : ENNReal) + Metric.ethickness ℝ X k ≤ (m : ENNReal) * Metric.ethickness ℝ X k) :
    volume (Metric.cthickening (a : ℝ) X)
      ≤ (cthickeningDoublingConst (Module.finrank ℝ E) m : ENNReal) * volume X := by
  rw [coe_cthickeningDoublingConst]
  have hc0 : (Metric.lt_volume_convexHull.c (Module.finrank ℝ E) : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr (Metric.lt_volume_convexHull.c_pos (Module.finrank ℝ E)).ne'
  have hctop : (Metric.lt_volume_convexHull.c (Module.finrank ℝ E) : ENNReal) ≠ ⊤ :=
    ENNReal.coe_ne_top
  have hprod : (∏ k ∈ Finset.range (Module.finrank ℝ E), Metric.ethickness ℝ X k)
      ≤ (Metric.lt_volume_convexHull.c (Module.finrank ℝ E) : ENNReal)⁻¹ * volume X := by
    rw [← ENNReal.div_eq_inv_mul]
    rw [ENNReal.le_div_iff_mul_le (Or.inl hc0) (Or.inl hctop)]
    simpa [mul_comm] using hX.ethickness_prod_le_volume
  calc
    volume (Metric.cthickening (a : ℝ) X)
        ≤ 2 ^ Module.finrank ℝ E *
            ∏ k ∈ Finset.range (Module.finrank ℝ E),
              ((a : ENNReal) + Metric.ethickness ℝ X k) := by
          exact volume_cthickening_le_prod_add X a
    _ ≤ 2 ^ Module.finrank ℝ E *
          ∏ k ∈ Finset.range (Module.finrank ℝ E),
            ((m : ENNReal) * Metric.ethickness ℝ X k) := by
          gcongr with k hk
          exact ha k hk
    _ = 2 ^ Module.finrank ℝ E * (m : ENNReal) ^ Module.finrank ℝ E *
          ∏ k ∈ Finset.range (Module.finrank ℝ E), Metric.ethickness ℝ X k := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
          ring
    _ ≤ 2 ^ Module.finrank ℝ E * (m : ENNReal) ^ Module.finrank ℝ E *
          ((Metric.lt_volume_convexHull.c (Module.finrank ℝ E) : ENNReal)⁻¹ * volume X) := by
          gcongr
    _ = (2 ^ Module.finrank ℝ E * (m : ENNReal) ^ Module.finrank ℝ E *
          (Metric.lt_volume_convexHull.c (Module.finrank ℝ E) : ENNReal)⁻¹) * volume X := by
          ring

/-- **Uniformity of the thickening ratio** (blueprint `lem:thickeningRatioUniform`): pairwise
comparable affine thicknesses make the ratio `|N_t(X)|/|X|` uniform over the family, up to the
absolute factor `M(n) = 2^{4n}/c_n²`. -/
private lemma volume_cthickening_mul_volume_le {X Y : Set E} (hX : Convex ℝ X) (hXne : X.Nonempty)
    (hY : Convex ℝ Y) (hYne : Y.Nonempty)
    (hXY : Metric.ethickness ℝ X ≤ 2 • Metric.ethickness ℝ Y)
    (hYX : Metric.ethickness ℝ Y ≤ 2 • Metric.ethickness ℝ X) (t : NNReal) :
    volume (Metric.cthickening (t : ℝ) X) * volume Y
      ≤ (thickeningRatioConst (Module.finrank ℝ E) : ENNReal) *
        (volume (Metric.cthickening (t : ℝ) Y) * volume X) := by
  have _hXne : X.Nonempty := hXne
  set n := Module.finrank ℝ E with hn_def
  set c : NNReal := Metric.lt_volume_convexHull.c n with hc_def
  set P := ∏ i ∈ Finset.range n, ((t : ENNReal) + Metric.ethickness ℝ X i) with hP_def
  set Q := ∏ i ∈ Finset.range n, ((t : ENNReal) + Metric.ethickness ℝ Y i) with hQ_def
  set R := ∏ i ∈ Finset.range n, Metric.ethickness ℝ X i with hR_def
  set S := ∏ i ∈ Finset.range n, Metric.ethickness ℝ Y i with hS_def
  -- The constant identity `M(n) · c_n² = 2^{4n}`.
  have hc0 : c ≠ 0 := by
    rw [hc_def]
    exact (Metric.lt_volume_convexHull.c_pos n).ne'
  have hM_nn : thickeningRatioConst n * c ^ 2 = 2 ^ (4 * n) := by
    unfold thickeningRatioConst
    rw [hc_def]
    rw [div_mul_cancel₀ (2 ^ (4 * n)) (pow_ne_zero 2 hc0)]
  have hM : (thickeningRatioConst n : ENNReal) * (c : ENNReal) ^ 2 = (2 ^ (4 * n) : ENNReal) := by
    rw [← ENNReal.coe_pow]
    rw [← ENNReal.coe_mul]
    rw [hM_nn]
    norm_cast
  have hpow4 : (2 ^ n * 2 ^ n * 2 ^ n * 2 ^ n : ENNReal) = 2 ^ (4 * n) := by
    rw [← pow_add, ← pow_add, ← pow_add]
    congr 1
    omega
  -- Pointwise comparability from `hXY` and `hYX`.
  have hXY_term : ∀ i, Metric.ethickness ℝ X i ≤ (2 : ENNReal) * Metric.ethickness ℝ Y i := by
    intro i
    simpa [Pi.smul_apply, nsmul_eq_mul] using hXY i
  have hYX_term : ∀ i, Metric.ethickness ℝ Y i ≤ (2 : ENNReal) * Metric.ethickness ℝ X i := by
    intro i
    simpa [Pi.smul_apply, nsmul_eq_mul] using hYX i
  have haddXY : ∀ i, (t : ENNReal) + Metric.ethickness ℝ X i
      ≤ (2 : ENNReal) * ((t : ENNReal) + Metric.ethickness ℝ Y i) := by
    intro i
    calc
      (t : ENNReal) + Metric.ethickness ℝ X i
          ≤ (t : ENNReal) + (2 : ENNReal) * Metric.ethickness ℝ Y i := by
            exact add_le_add_right (hXY_term i) (t : ENNReal)
      _ ≤ (2 : ENNReal) * (t : ENNReal) + (2 : ENNReal) * Metric.ethickness ℝ Y i := by
            have ht_le : (t : ENNReal) ≤ (2 : ENNReal) * (t : ENNReal) := by
              calc
                (t : ENNReal) ≤ (t : ENNReal) + (t : ENNReal) := le_self_add
                _ = (2 : ENNReal) * (t : ENNReal) := by rw [two_mul]
            exact add_le_add_left ht_le ((2 : ENNReal) * Metric.ethickness ℝ Y i)
      _ = (2 : ENNReal) * ((t : ENNReal) + Metric.ethickness ℝ Y i) := by
            rw [← mul_add]
  -- Upper and lower volume bounds via the four product estimates.
  have hUpX : volume (Metric.cthickening (t : ℝ) X) ≤ (2 ^ n : ENNReal) * P := by
    simpa [P, n] using (volume_cthickening_le_prod_add X t)
  have hUpY : volume Y ≤ (2 ^ n : ENNReal) * S := by
    simpa [S, n] using (volume_le_prod_ethickness Y)
  have hLpX : (c : ENNReal) * R ≤ volume X := by
    simpa [R, n, c] using (hX.ethickness_prod_le_volume)
  have hLpY : (c : ENNReal) * Q ≤ volume (Metric.cthickening (t : ℝ) Y) := by
    simpa [Q, n, c] using (prod_add_le_volume_cthickening hY hYne t)
  -- Product comparabilities.
  have hP_le : P ≤ (2 ^ n : ENNReal) * Q := by
    calc
      P = ∏ i ∈ Finset.range n, ((t : ENNReal) + Metric.ethickness ℝ X i) := rfl
      _ ≤ ∏ i ∈ Finset.range n, ((2 : ENNReal) * ((t : ENNReal) + Metric.ethickness ℝ Y i)) := by
        gcongr with i hi
        exact haddXY i
      _ = (2 ^ n : ENNReal) * Q := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  have hS_le : S ≤ (2 ^ n : ENNReal) * R := by
    calc
      S = ∏ i ∈ Finset.range n, Metric.ethickness ℝ Y i := rfl
      _ ≤ ∏ i ∈ Finset.range n, ((2 : ENNReal) * Metric.ethickness ℝ X i) := by
        gcongr with i hi
        exact hYX_term i
      _ = (2 ^ n : ENNReal) * R := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  have hLHS_main : volume (Metric.cthickening (t : ℝ) X) * volume Y
      ≤ (2 ^ (4 * n) : ENNReal) * Q * R := by
    calc
      volume (Metric.cthickening (t : ℝ) X) * volume Y
          ≤ ((2 ^ n : ENNReal) * P) * ((2 ^ n : ENNReal) * S) := by
            exact mul_le_mul hUpX hUpY (by simp) (by simp)
      _ = (2 ^ n : ENNReal) * (2 ^ n : ENNReal) * (P * S) := by
            ring
      _ ≤ (2 ^ n : ENNReal) * (2 ^ n : ENNReal) *
          (((2 ^ n : ENNReal) * Q) * ((2 ^ n : ENNReal) * R)) := by
            exact mul_le_mul_right
              (mul_le_mul hP_le hS_le (by simp) (by simp)) ((2 ^ n : ENNReal) * (2 ^ n : ENNReal))
      _ = (2 ^ n * 2 ^ n * 2 ^ n * 2 ^ n : ENNReal) * (Q * R) := by
            ring
      _ = (2 ^ (4 * n) : ENNReal) * Q * R := by
            rw [hpow4]
            ring
  have hRHS_lb : ((c : ENNReal) * Q) * ((c : ENNReal) * R)
      ≤ volume (Metric.cthickening (t : ℝ) Y) * volume X := by
    exact mul_le_mul hLpY hLpX (by simp) (by simp)
  have hM_comb : (2 ^ (4 * n) : ENNReal) * Q * R =
      (thickeningRatioConst n : ENNReal) * (((c : ENNReal) * Q) * ((c : ENNReal) * R)) := by
    rw [← hM]
    ring
  calc
    volume (Metric.cthickening (t : ℝ) X) * volume Y
        ≤ (2 ^ (4 * n) : ENNReal) * Q * R := hLHS_main
    _ = (thickeningRatioConst n : ENNReal) * (((c : ENNReal) * Q) * ((c : ENNReal) * R)) := hM_comb
    _ ≤ (thickeningRatioConst n : ENNReal) *
        (volume (Metric.cthickening (t : ℝ) Y) * volume X) := by
          exact mul_le_mul (le_refl _) hRHS_lb (by simp) (by simp)

/-- Pure `ℝ≥0∞` bookkeeping for the single-body reduction: given the LHS volume relation
`|Ñ| ≤ 4r|Kπ|`, the affine Cordoba bound for the projected family at proportion
`c_th·lam·D⁻²` with Frostman constant `D·(L·κ·C)` and eccentricity exponent `N + 16`, and the RHS
fibre lift `r|Sπ| ≤ |iSh|`, the target inequality follows by algebra. This isolates the
constant-matching arithmetic from the geometry. -/
private lemma assemble_bound {c₂ cth D L κ C lam volKtilde volKpi volSpi volISh r : ENNReal}
    {N : ℕ}
    (hc₂0 : c₂ ≠ 0) (hc₂top : c₂ ≠ ⊤) (hcth0 : cth ≠ 0) (hcthtop : cth ≠ ⊤)
    (hD0 : D ≠ 0) (hDtop : D ≠ ⊤)
    (hLHS : volKtilde ≤ 2 * (2 * r) * volKpi)
    (hCordoba : c₂ * (cth * lam * D⁻¹ * D⁻¹) ^ 2 * volKpi
      ≤ (((N + 16 : ℕ) : ENNReal) + 1) * (D * (L * κ * C)) * volSpi)
    (hRHS : r * volSpi ≤ volISh) :
    C⁻¹ * lam ^ 2 * volKtilde
      ≤ 68 * c₂⁻¹ * cth⁻¹ ^ 2 * D ^ 5 * L * κ * ((N : ENNReal) + 1) * volISh := by
  -- Normalize the LHS fibre factor `2 * (2 * r) = 4 * r`.
  have hLHS' : volKtilde ≤ 4 * r * volKpi := by
    calc
      volKtilde ≤ 2 * (2 * r) * volKpi := hLHS
      _ = 4 * r * volKpi := by ring
  -- `(N + 16) + 1 ≤ 17 * (N + 1)`, so the eccentricity factor is bounded by `17 * (N + 1)`.
  have hN17 : (((N + 16 : ℕ) : ENNReal) + 1) ≤ 17 * ((N : ENNReal) + 1) := by
    exact_mod_cast (by omega : (N + 16) + 1 ≤ 17 * (N + 1))
  -- Cordoba bound with the eccentricity factor replaced by its upper bound.
  have hCordoba₁ : c₂ * (cth * lam * D⁻¹ * D⁻¹) ^ 2 * volKpi
      ≤ 17 * ((N : ENNReal) + 1) * (D * (L * κ * C)) * volSpi := by
    calc
      c₂ * (cth * lam * D⁻¹ * D⁻¹) ^ 2 * volKpi
          ≤ (((N + 16 : ℕ) : ENNReal) + 1) * (D * (L * κ * C)) * volSpi := hCordoba
      _ ≤ 17 * ((N : ENNReal) + 1) * (D * (L * κ * C)) * volSpi := by
          gcongr
  -- Combine the LHS volume relation with the Cordoba bound (multiplying the latter by `4 * r`).
  have hMain : c₂ * (cth * lam * D⁻¹ * D⁻¹) ^ 2 * volKtilde
      ≤ 4 * r * (17 * ((N : ENNReal) + 1) * (D * (L * κ * C))) * volSpi := by
    calc
      c₂ * (cth * lam * D⁻¹ * D⁻¹) ^ 2 * volKtilde
          ≤ c₂ * (cth * lam * D⁻¹ * D⁻¹) ^ 2 * (4 * r * volKpi) := by
            exact mul_le_mul_right hLHS' (c₂ * (cth * lam * D⁻¹ * D⁻¹) ^ 2)
      _ = (4 * r) * (c₂ * (cth * lam * D⁻¹ * D⁻¹) ^ 2 * volKpi) := by ring
      _ ≤ (4 * r) * (17 * ((N : ENNReal) + 1) * (D * (L * κ * C)) * volSpi) := by
            exact mul_le_mul_right hCordoba₁ (4 * r)
      _ = 4 * r * (17 * ((N : ENNReal) + 1) * (D * (L * κ * C))) * volSpi := by ring
  -- Replace `r * volSpi` by `volISh` using the RHS fibre lift; `4 * 17 = 68`.
  have hMain₂ : c₂ * (cth * lam * D⁻¹ * D⁻¹) ^ 2 * volKtilde
      ≤ 4 * 17 * ((N : ENNReal) + 1) * D * (L * κ * C) * volISh := by
    calc
      c₂ * (cth * lam * D⁻¹ * D⁻¹) ^ 2 * volKtilde
          ≤ 4 * r * (17 * ((N : ENNReal) + 1) * (D * (L * κ * C))) * volSpi := hMain
      _ = 4 * 17 * ((N : ENNReal) + 1) * D * (L * κ * C) * (r * volSpi) := by ring
      _ ≤ 4 * 17 * ((N : ENNReal) + 1) * D * (L * κ * C) * volISh := by
          exact mul_le_mul_right hRHS (4 * 17 * ((N : ENNReal) + 1) * D * (L * κ * C))
  -- Power forms of the cancellation facts needed below.
  have hcth_pow : cth⁻¹ ^ 2 * cth ^ 2 = 1 := by
    calc
      cth⁻¹ ^ 2 * cth ^ 2 = (cth⁻¹ * cth) ^ 2 := by ring
      _ = 1 := by rw [ENNReal.inv_mul_cancel hcth0 hcthtop]; norm_num
  have hD_pow : D ^ 4 * (D⁻¹) ^ 4 = 1 := by
    calc
      D ^ 4 * (D⁻¹) ^ 4 = (D * D⁻¹) ^ 4 := by ring
      _ = 1 := by rw [ENNReal.mul_inv_cancel hD0 hDtop]; norm_num
  -- Multiply the main bound by `c₂⁻¹ * cth⁻¹² * D⁴ * C⁻¹`: the left side collapses to
  -- `C⁻¹ * lam² * volKtilde`.
  have hLHS_simp : c₂⁻¹ * cth⁻¹ ^ 2 * D ^ 4 * C⁻¹ * (c₂ * (cth * lam * D⁻¹ * D⁻¹) ^ 2 * volKtilde)
      = C⁻¹ * lam ^ 2 * volKtilde := by
    rw [show c₂⁻¹ * cth⁻¹ ^ 2 * D ^ 4 * C⁻¹ * (c₂ * (cth * lam * D⁻¹ * D⁻¹) ^ 2 * volKtilde)
        = (c₂⁻¹ * c₂) * (cth⁻¹ ^ 2 * cth ^ 2) * (D ^ 4 * (D⁻¹) ^ 4) * C⁻¹ * lam ^ 2 *
          volKtilde by ring]
    rw [ENNReal.inv_mul_cancel hc₂0 hc₂top, hcth_pow, hD_pow]
    ring
  -- The right side after the same multiplication is bounded by the target constant using
  -- `C⁻¹ * C ≤ 1`.
  have hRHS_simp :
      c₂⁻¹ * cth⁻¹ ^ 2 * D ^ 4 * C⁻¹ *
        (4 * 17 * ((N : ENNReal) + 1) * D * (L * κ * C) * volISh)
      ≤ 68 * c₂⁻¹ * cth⁻¹ ^ 2 * D ^ 5 * L * κ * ((N : ENNReal) + 1) * volISh := by
    calc
      c₂⁻¹ * cth⁻¹ ^ 2 * D ^ 4 * C⁻¹ *
          (4 * 17 * ((N : ENNReal) + 1) * D * (L * κ * C) * volISh)
          = (C⁻¹ * C) *
            (4 * 17 * c₂⁻¹ * cth⁻¹ ^ 2 * (D ^ 4 * D) * (L * κ) *
              ((N : ENNReal) + 1) * volISh) := by ring
      _ ≤ 1 * (4 * 17 * c₂⁻¹ * cth⁻¹ ^ 2 * (D ^ 4 * D) * (L * κ) *
          ((N : ENNReal) + 1) * volISh) := by
          exact mul_le_mul' (ENNReal.inv_mul_le_one C) le_rfl
      _ = 68 * c₂⁻¹ * cth⁻¹ ^ 2 * D ^ 5 * L * κ * ((N : ENNReal) + 1) * volISh := by ring
  -- Assemble.
  calc
    C⁻¹ * lam ^ 2 * volKtilde
        = c₂⁻¹ * cth⁻¹ ^ 2 * D ^ 4 * C⁻¹ *
            (c₂ * (cth * lam * D⁻¹ * D⁻¹) ^ 2 * volKtilde) := hLHS_simp.symm
    _ ≤ c₂⁻¹ * cth⁻¹ ^ 2 * D ^ 4 * C⁻¹ *
        (4 * 17 * ((N : ENNReal) + 1) * D * (L * κ * C) * volISh) := by
        exact mul_le_mul' le_rfl hMain₂
    _ ≤ 68 * c₂⁻¹ * cth⁻¹ ^ 2 * D ^ 5 * L * κ * ((N : ENNReal) + 1) * volISh := hRHS_simp

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- In `ℝ³`, the shortest affine thickness of `K` is attained by a genuinely two-dimensional,
nonempty affine subspace: there is `A` with `finrank ℝ A.direction = 2` and
`K.carrier ⊆ N_r(A)` for `r = thickness ℝ K.carrier 2`. This packages the affine-subspace setup of
the projection reduction. Follows from `Metric.exists_subset_cthickening_thickness_finrank_eq` at
`j = 2 ≤ 3 = finrank ℝ E`. -/
private lemma exists_twoDim_slab (K : ConvexSpaceBody E) (hdim : Module.finrank ℝ E = 3) :
    ∃ A : AffineSubspace ℝ E, (A : Set E).Nonempty ∧ Module.finrank ℝ A.direction = 2 ∧
      K.carrier ⊆ Metric.cthickening (Metric.thickness ℝ K.carrier 2) A := by
  have hK_bdd : Bornology.IsBounded K.carrier :=
    K.isCompact.isBounded
  have hK_ne : (K.carrier).Nonempty := K.nonempty
  have hj : (2 : ℕ) ≤ Module.finrank ℝ E := by
    rw [hdim]
    norm_num
  obtain ⟨A, hAne, hAdim, hAsub⟩ :=
    Metric.exists_subset_cthickening_thickness_finrank_eq hK_bdd hK_ne hj
  exact ⟨A, hAne, hAdim, hAsub⟩

omit [Nontrivial E] in
/-- LHS volume relation of the projection reduction: the enlarged carrier `N_r(K)` has volume at
most the slab-fiber factor times the volume of its shadow. Direct from
`volume_le_two_mul_volume_orthogonalProjection_image` (the slab radius of `N_r(K)` is `2r` since
`K ⊆ N_r(A)`). Deferred. -/
private lemma lhs_proj_le {A : AffineSubspace ℝ E} [Nonempty A] (K : ConvexSpaceBody E)
    (hcodim : Module.finrank ℝ E = Module.finrank ℝ A.direction + 1)
    (hAsub : K.carrier ⊆
      Metric.cthickening (Metric.thickness ℝ K.carrier (Module.finrank ℝ E - 1)) A) :
    volume (K.cthickening (Metric.thickness ℝ K.carrier (Module.finrank ℝ E - 1))).carrier
      ≤ 2 * (2 * ENNReal.ofReal (Metric.thickness ℝ K.carrier (Module.finrank ℝ E - 1))) *
          volume (orthogonalProjection A ''
            (K.cthickening (Metric.thickness ℝ K.carrier (Module.finrank ℝ E - 1))).carrier) := by
  set r0 := Metric.thickness ℝ K.carrier (Module.finrank ℝ E - 1) with hr0
  have hr0_nonneg : 0 ≤ r0 := Metric.thickness_nonneg _ _
  have hcarrier_eq : (K.cthickening r0).carrier = Metric.cthickening r0 K.carrier := by
    simp
  have h_cont : (K.cthickening r0).carrier ⊆ Metric.cthickening (2*r0) (A : Set E) := by
    rw [hcarrier_eq]
    calc
      Metric.cthickening r0 K.carrier ⊆ Metric.cthickening r0 (Metric.cthickening r0 (A : Set E)) :=
        Metric.cthickening_subset_of_subset r0 hAsub
      _ ⊆ Metric.cthickening (r0 + r0) (A : Set E) :=
        Metric.cthickening_cthickening_subset hr0_nonneg hr0_nonneg _
      _ = Metric.cthickening (2*r0) (A : Set E) := by ring_nf
  set r' : NNReal := ⟨2 * r0, mul_nonneg (by norm_num) hr0_nonneg⟩ with hr'
  have h_cont' : (K.cthickening r0).carrier ⊆ Metric.cthickening (r' : ℝ) (A : Set E) := by
    dsimp [r']
    exact h_cont
  have h_main := volume_le_two_mul_volume_orthogonalProjection_image A hcodim (r := r')
    (s := (K.cthickening r0).carrier) h_cont'
  have hr'_val : (r' : ENNReal) = 2 * ENNReal.ofReal r0 := by
    calc
      (r' : ENNReal) = ENNReal.ofReal (r' : ℝ) :=
        (ENNReal.ofReal_coe_nnreal (p := r')).symm
      _ = ENNReal.ofReal (2*r0) := by
        rw [show (r' : ℝ) = 2*r0 from by dsimp [r']; rfl]
      _ = ENNReal.ofReal (2 : ℝ) * ENNReal.ofReal r0 := by
        rw [ENNReal.ofReal_mul (by norm_num : 0 ≤ (2 : ℝ))]
      _ = (2 : ENNReal) * ENNReal.ofReal r0 := by norm_num
  apply h_main.trans
  rw [hr'_val]

/-! ### Slab geometry: affine thickness of shadows -/

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **Shadow thickness lower bound** (blueprint `lem:thicknessSlabShadow`): a set inside the
slab `N_ρ(H)` is contained in the `ρ`-neighbourhood of its own shadow, so its affine thickness
exceeds the shadow's by at most `ρ`. The shadow's thickness is computed inside `↑H`; passing to
`E` only decreases it, because the inclusion `↑H → E` is an affine isometry. -/
private lemma ethickness_le_add_ethickness_image_orthogonalProjection
    {A : AffineSubspace ℝ E} [Nonempty ↑A] {S : Set E} {ρ : NNReal}
    (hS : S ⊆ Metric.cthickening (ρ : ℝ) (A : Set E)) (k : ℕ) :
    Metric.ethickness ℝ S k
      ≤ (ρ : ENNReal) + Metric.ethickness ℝ (orthogonalProjection A '' S) k := by
  have hS' : S ⊆ Metric.cthickening (ρ : ℝ) (Subtype.val '' (orthogonalProjection A '' S)) := by
    intro x hx
    have hxN : x ∈ Metric.cthickening (ρ : ℝ) (A : Set E) := hS hx
    have hx_infDist_le_ρ : Metric.infDist x (A : Set E) ≤ (ρ : ℝ) := by
      have hx_infEDist : Metric.infEDist x (A : Set E) ≤ ENNReal.ofReal (ρ : ℝ) :=
        Metric.mem_cthickening_iff.mp hxN
      rw [Metric.infDist, ← ENNReal.toReal_ofReal (NNReal.coe_nonneg ρ)]
      exact ENNReal.toReal_mono (by exact ENNReal.ofReal_ne_top) hx_infEDist
    have hdist : dist x (orthogonalProjection A x : E) ≤ (ρ : ℝ) := by
      calc
        dist x (orthogonalProjection A x : E) = Metric.infDist x (A : Set E) :=
          EuclideanGeometry.dist_orthogonalProjection_eq_infDist A x
        _ ≤ (ρ : ℝ) := hx_infDist_le_ρ
    exact Metric.mem_cthickening_of_dist_le x (orthogonalProjection A x : E) (ρ : ℝ)
      (Subtype.val '' (orthogonalProjection A '' S))
      (Set.mem_image_of_mem Subtype.val (Set.mem_image_of_mem (orthogonalProjection A) hx)) hdist
  have h1 : Metric.ethickness ℝ S k
      ≤ (ρ : ENNReal) + Metric.ethickness ℝ (Subtype.val '' (orthogonalProjection A '' S)) k :=
    (Metric.ethickness_monotone hS' k).trans (Metric.ethickness_cthickening_le ρ k)
  have h2 : Metric.ethickness ℝ (Subtype.val '' (orthogonalProjection A '' S)) k
      ≤ Metric.ethickness ℝ (orthogonalProjection A '' S) k := by
    have hL : LipschitzWith 1 (A.subtypeₐᵢ : ↥A → E) := A.subtypeₐᵢ.isometry.lipschitz
    have himg := (LipschitzWith.ethickness_image_le (f := (A.subtypeₐᵢ.toAffineMap : ↥A →ᵃ[ℝ] E))
      hL (orthogonalProjection A '' S)) k
    simpa [one_smul] using himg
  exact h1.trans (add_le_add (le_refl (ρ : ENNReal)) h2)

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **The shadow of a thickening contains the thickened shadow** (blueprint
`lem:shadowOfThickening`): if `y ∈ ↑H` is within `t` of `π(X)`, translate a nearest point of `X`
by the vector `y - π(x)`, which lies in `H.direction`, to obtain a point of `N_t(X)` projecting
to `y`. -/
private lemma cthickening_image_orthogonalProjection_subset
    {A : AffineSubspace ℝ E} [Nonempty ↑A] {X : Set E} (hX : IsCompact X) (hXne : X.Nonempty)
    {t : ℝ} (ht : 0 ≤ t) :
    Metric.cthickening t (orthogonalProjection A '' X)
      ⊆ orthogonalProjection A '' Metric.cthickening t X := by
  intro y hy
  -- y ∈ cthickening t (π '' X): the shadow of X is compact, so it has a nearest point π x
  have hπX_compact : IsCompact (orthogonalProjection A '' X) :=
    hX.image (orthogonalProjection A).continuous
  have hπX_ne : (orthogonalProjection A '' X).Nonempty := hXne.image _
  have hinfEDist : Metric.infEDist y (orthogonalProjection A '' X) ≤ ENNReal.ofReal t :=
    (Metric.mem_cthickening_iff.mp hy)
  obtain ⟨z, hz, hz_eq⟩ := hπX_compact.exists_infEDist_eq_edist hπX_ne y
  have hdist_le_t : dist y z ≤ t := by
    have hle : edist y z ≤ ENNReal.ofReal t := by
      rw [← hz_eq]
      exact hinfEDist
    rw [edist_dist] at hle
    exact (ENNReal.ofReal_le_ofReal_iff ht).mp hle
  obtain ⟨x, hx, rfl⟩ := hz
  -- Translate x by the vector y - π x, which lies in A.direction.
  let v : E := (y : E) -ᵥ (orthogonalProjection A x : E)
  let x' : E := x +ᵥ v
  have hx'_dist : dist x' x ≤ t := by
    calc
      dist x' x = ‖x' -ᵥ x‖ := by rw [dist_eq_norm_vsub]
      _ = ‖v‖ := by simp [x', v, vadd_eq_add, vsub_eq_sub]
      _ = dist (y : E) (orthogonalProjection A x : E) := by
        rw [dist_eq_norm_vsub]
      _ = dist y (orthogonalProjection A x) := rfl
      _ ≤ t := hdist_le_t
  have hx'_cth : x' ∈ Metric.cthickening t X :=
    Metric.mem_cthickening_of_dist_le x' x t X hx hx'_dist
  have hx'vsub : x' -ᵥ (y : E) ∈ A.directionᗮ := by
    have hxy : x' -ᵥ (y : E) = x -ᵥ (orthogonalProjection A x : E) := by
      simp [x', v, vadd_eq_add, vsub_eq_sub]
      abel
    rw [hxy]
    exact vsub_orthogonalProjection_mem_direction_orthogonal A x
  have hproj : orthogonalProjection A x' = y := by
    calc
      orthogonalProjection A x' = orthogonalProjection A (y : E) := by
        rw [orthogonalProjection_eq_orthogonalProjection_iff_vsub_mem.mpr hx'vsub]
      _ = y := by
        exact Subtype.ext (orthogonalProjection_eq_self_iff.mpr y.2)
  exact ⟨x', hx'_cth, hproj⟩

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- Consequence of `cthickening_image_orthogonalProjection_subset`: thickening a body at scale `t`
raises the affine thickness of its shadow by at least `t`. -/
private lemma le_ethickness_image_orthogonalProjection_cthickening
    {A : AffineSubspace ℝ E} [Nonempty ↑A] {X : Set E} (hX : IsCompact X) (hXne : X.Nonempty)
    {t : NNReal} {k : ℕ} (hk : k < Module.finrank ℝ A.direction) :
    (t : ENNReal) + Metric.ethickness ℝ (orthogonalProjection A '' X) k
      ≤ Metric.ethickness ℝ (orthogonalProjection A '' Metric.cthickening (t : ℝ) X) k := by
  have hsub : Metric.cthickening (t : ℝ) (orthogonalProjection A '' X)
      ⊆ orthogonalProjection A '' Metric.cthickening (t : ℝ) X :=
    cthickening_image_orthogonalProjection_subset hX hXne t.coe_nonneg
  have hne : (orthogonalProjection A '' X).Nonempty := hXne.image _
  have hle : Metric.ethickness ℝ (orthogonalProjection A '' X) k + ENNReal.ofReal (t : ℝ)
      ≤ Metric.ethickness ℝ (Metric.cthickening (t : ℝ) (orthogonalProjection A '' X)) k :=
    le_ethickness_cthickening hne (ρ := (t : ℝ)) hk
  calc
    (t : ENNReal) + Metric.ethickness ℝ (orthogonalProjection A '' X) k
        ≤ Metric.ethickness ℝ (Metric.cthickening (t : ℝ) (orthogonalProjection A '' X)) k := by
          simpa [ENNReal.ofReal_coe_nnreal, add_comm] using hle
    _ ≤ Metric.ethickness ℝ (orthogonalProjection A '' Metric.cthickening (t : ℝ) X) k :=
        Metric.ethickness_monotone hsub k

omit [Nontrivial E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Thickening a subset of a slab stays in a slightly wider slab. -/
private lemma cthickening_subset_cthickening_affineSubspace {A : AffineSubspace ℝ E} {X : Set E}
    {a b : NNReal} (h : X ⊆ Metric.cthickening (b : ℝ) (A : Set E)) :
    Metric.cthickening (a : ℝ) X ⊆ Metric.cthickening ((a + b : NNReal) : ℝ) (A : Set E) := by
  calc
    Metric.cthickening (a : ℝ) X
        ⊆ Metric.cthickening (a : ℝ) (Metric.cthickening (b : ℝ) (A : Set E)) :=
      Metric.cthickening_subset_of_subset (a : ℝ) h
    _ ⊆ Metric.cthickening ((a : ℝ) + (b : ℝ)) (A : Set E) :=
      Metric.cthickening_cthickening_subset (NNReal.coe_nonneg a) (NNReal.coe_nonneg b)
        (A : Set E)
    _ = Metric.cthickening ((a + b : NNReal) : ℝ) (A : Set E) := by
      rw [← NNReal.coe_add]

/-! ### The slab product body -/

/-- The **slab product body** over the shadow of `K`: the full part of the slab `N_ρ(H)` lying over
`π(K)` (blueprint `def:slabProductBody`). It contains `K`, has the same shadow, and - unlike `K`
itself - satisfies the product hypothesis `eq:projectionProductBody` required to project a
Frostman family. -/
private noncomputable def slabProductBody (A : AffineSubspace ℝ E) [Nonempty ↑A]
    (K : ConvexSpaceBody E) (ρ : NNReal)
    (hK : K.carrier ⊆ Metric.cthickening (ρ : ℝ) (A : Set E)) : ConvexSpaceBody E where
  carrier := (orthogonalProjection A ⁻¹' (orthogonalProjection A '' K.carrier)) ∩
    Metric.cthickening (ρ : ℝ) (A : Set E)
  convex' := by
    -- π⁻¹(π '' K.carrier) is convex: the preimage under the affine map π of the convex shadow
    -- of K. The ρ-thickening of the affine subspace A is convex.
    have hpre : Convexity.IsConvexSet ℝ
        (orthogonalProjection A ⁻¹' (orthogonalProjection A '' K.carrier)) :=
      Convexity.IsConvexSet.affineMap_preimage (orthogonalProjection A).toAffineMap
        (K.orthogonalProjectionImage A).convex'
    have hcth : Convexity.IsConvexSet ℝ (Metric.cthickening (ρ : ℝ) (A : Set E)) :=
      (A.convex.cthickening (ρ : ℝ)).isConvexSet
    exact hpre.inter hcth
  isCompact' := by
    let S : Set E :=
      (orthogonalProjection A ⁻¹' (orthogonalProjection A '' K.carrier)) ∩
        Metric.cthickening (ρ : ℝ) (A : Set E)
    change IsCompact S
    -- Closed: preimage under the continuous π of the compact (hence closed) shadow, intersected
    -- with the closed ρ-thickening of A.
    have hclosed₁ : IsClosed
        (orthogonalProjection A ⁻¹' (orthogonalProjection A '' K.carrier)) :=
      (K.orthogonalProjectionImage A).isCompact.isClosed.preimage (orthogonalProjection A).cont
    have hclosed₂ : IsClosed (Metric.cthickening (ρ : ℝ) (A : Set E)) :=
      Metric.isClosed_cthickening
    have hclosed : IsClosed S := by
      simpa [S] using hclosed₁.inter hclosed₂
    -- Bounded: the carrier lies in the 2ρ-thickening of the compact carrier of K.
    have hsub : S ⊆ Metric.cthickening (2 * (ρ : ℝ)) K.carrier := by
      intro x hx
      exact (preimage_image_orthogonalProjection_inter_cthickening_subset_cthickening
        (H := A) (r := (ρ : ℝ)) (s := K.carrier) (ρ.coe_nonneg) hK) (by simpa [S] using hx)
    have hbdd_compact : IsCompact (Metric.cthickening (2 * (ρ : ℝ)) K.carrier) :=
      Metric.isCompact_of_isClosed_isBounded Metric.isClosed_cthickening
        (K.isCompact.isBounded.cthickening)
    have hbdd : Bornology.IsBounded (Metric.cthickening (2 * (ρ : ℝ)) K.carrier) :=
      IsCompact.isBounded hbdd_compact
    have hbdd' : Bornology.IsBounded S := hbdd.subset hsub
    exact Metric.isCompact_of_isClosed_isBounded hclosed hbdd'
  nonempty' := by
    obtain ⟨x, hx⟩ := K.nonempty
    refine ⟨x, ?_, ?_⟩
    · rw [Set.mem_preimage]
      exact Set.mem_image_of_mem (orthogonalProjection A) hx
    · exact hK hx

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- The slab product body contains `K`. -/
private lemma le_slabProductBody {A : AffineSubspace ℝ E} [Nonempty ↑A]
    (K : ConvexSpaceBody E) {ρ : NNReal}
    (hK : K.carrier ⊆ Metric.cthickening (ρ : ℝ) (A : Set E)) :
    K ≤ slabProductBody A K ρ hK := by
  rw [SetLike.le_def]
  intro x hx
  exact ⟨Set.mem_preimage.mpr (Set.mem_image_of_mem (orthogonalProjection A) hx), hK hx⟩

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- The slab product body has the same shadow as `K`. -/
private lemma image_slabProductBody {A : AffineSubspace ℝ E} [Nonempty ↑A]
    (K : ConvexSpaceBody E) {ρ : NNReal}
    (hK : K.carrier ⊆ Metric.cthickening (ρ : ℝ) (A : Set E)) :
    orthogonalProjection A '' (slabProductBody A K ρ hK).carrier
      = orthogonalProjection A '' K.carrier := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact hx.1
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, (le_slabProductBody (A := A) K hK) hx, rfl⟩

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- The slab product body satisfies the product hypothesis `eq:projectionProductBody`. -/
private lemma slabProductBody_product {A : AffineSubspace ℝ E} [Nonempty ↑A]
    (K : ConvexSpaceBody E) {ρ : NNReal}
    (hK : K.carrier ⊆ Metric.cthickening (ρ : ℝ) (A : Set E)) :
    (slabProductBody A K ρ hK).carrier =
      (orthogonalProjection A ⁻¹'
          (orthogonalProjection A '' (slabProductBody A K ρ hK).carrier)) ∩
        Metric.cthickening (ρ : ℝ) (A : Set E) := by
  rw [image_slabProductBody]
  rfl

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- The slab product body over `K` lies in `N_{2ρ}(K)`. -/
private lemma slabProductBody_subset_cthickening {A : AffineSubspace ℝ E} [Nonempty ↑A]
    (K : ConvexSpaceBody E) {ρ : NNReal}
    (hK : K.carrier ⊆ Metric.cthickening (ρ : ℝ) (A : Set E)) :
    (slabProductBody A K ρ hK).carrier ⊆ Metric.cthickening ((2 * ρ : NNReal) : ℝ) K.carrier := by
  intro x hx
  change x ∈ (orthogonalProjection A ⁻¹' (orthogonalProjection A '' K.carrier)) ∩
      Metric.cthickening (ρ : ℝ) (A : Set E) at hx
  exact (preimage_image_orthogonalProjection_inter_cthickening_subset_cthickening
    (H := A) (r := (ρ : ℝ)) (s := K.carrier) (ρ.coe_nonneg) hK) hx

/-! ### The thickened inner family -/

/-- The inner convex bodies of the reduction, thickened at scale `2r`. -/
private noncomputable abbrev thickBody (rn : NNReal) (W : ConvexSpaceBody E) : ConvexSpaceBody E :=
  W.cthickening ((2 * rn : NNReal) : ℝ)

/-- The inner shaded bodies of the reduction: the carrier is thickened at scale `2r` (which makes
the shadows' affine thicknesses pairwise comparable and makes the reverse projection comparison
available), while the shading is thickened only at scale `r/2` (so that the lifted union still fits
inside the induced shading `N_{2r}(U) ∩ N_r(K)`). The two radii differ by the fixed factor `4`, so
the shading proportion is preserved up to an absolute constant. -/
private noncomputable def thickShaded (rn : NNReal) (S : ShadedBody E) : ShadedBody E where
  toConvexSpaceBody := thickBody rn S.toConvexSpaceBody
  shade := Metric.cthickening ((rn / 2 : NNReal) : ℝ) S.shade
  measurableSet_shade := Metric.isClosed_cthickening.measurableSet
  shade_subset := by
    calc
      Metric.cthickening ((rn / 2 : NNReal) : ℝ) S.shade
          ⊆ Metric.cthickening ((rn / 2 : NNReal) : ℝ) S.carrier :=
        Metric.cthickening_subset_of_subset ((rn / 2 : NNReal) : ℝ) S.shade_subset
      _ ⊆ Metric.cthickening ((2 * rn : NNReal) : ℝ) S.carrier := by
        apply Metric.cthickening_mono
        have hle : (rn / 2 : NNReal) ≤ 2 * rn := by
          calc
            (rn / 2 : NNReal) ≤ rn := by
              exact div_le_self (by positivity) (by norm_num : (1 : NNReal) ≤ 2)
            _ ≤ 2 * rn := by
              exact le_mul_of_one_le_left (by positivity) (by norm_num : (1 : NNReal) ≤ 2)
        exact_mod_cast hle
      _ = (thickBody rn S.toConvexSpaceBody).carrier := by
        simp [thickBody]

omit [Nontrivial E] in
private lemma isClosed_thickShaded_shade (rn : NNReal) (S : ShadedBody E) :
    IsClosed (thickShaded rn S).shade := Metric.isClosed_cthickening

/-! ### The projection inputs -/

/-- **Reverse projection comparison** (blueprint `lem:reverseProjectionComparison`, the instance of
Equation~`eq:projectionVolumeComparison` used here): a body thickened at scale `2r` inside the slab
`N_{3r}(H)` satisfies `6r|π(V)| ≤ D|V|`, because the full part of the slab over its shadow lies in
`N_{6r}` of it, hence in `N_{8r}` of the unthickened body, and `8r ≤ 4·(2r)`. -/
private lemma revProj {A : AffineSubspace ℝ E} [Nonempty ↑A]
    (hdim : Module.finrank ℝ E = 3)
    (hcodim : Module.finrank ℝ E = Module.finrank ℝ A.direction + 1)
    (W : ConvexSpaceBody E) {rn : NNReal}
    (hslab : (thickBody rn W).carrier
      ⊆ Metric.cthickening ((3 * rn : NNReal) : ℝ) (A : Set E)) :
    2 * ((3 * rn : NNReal) : ENNReal) *
        volume ((thickBody rn W).orthogonalProjectionImage A).carrier
      ≤ (projectionVolumeComparisonConst : ENNReal) * volume (thickBody rn W).carrier := by
  -- Step 1: the slab product body over `V = thickBody rn W` has exactly the volume
  -- `2·(3rn)·|π V|`.
  have hPvol_eq : volume (slabProductBody A (thickBody rn W) (3 * rn) hslab).carrier
      = 2 * ((3 * rn : NNReal) : ENNReal) *
          volume ((thickBody rn W).orthogonalProjectionImage A).carrier := by
    change volume ((orthogonalProjection A ⁻¹'
        (orthogonalProjection A '' (thickBody rn W).carrier)) ∩
        Metric.cthickening ((3 * rn : NNReal) : ℝ) (A : Set E))
      = 2 * ((3 * rn : NNReal) : ENNReal) *
        volume ((thickBody rn W).orthogonalProjectionImage A).carrier
    rw [← ConvexSpaceBody.coe_orthogonalProjectionImage]
    exact volume_preimage_orthogonalProjection_inter_cthickening A hcodim
      ((thickBody rn W).orthogonalProjectionImage A) (3 * rn)
  -- Step 2: the slab product body lies in `N_{8rn}(W)`.
  have hsub : (slabProductBody A (thickBody rn W) (3 * rn) hslab).carrier
      ⊆ Metric.cthickening ((8 * rn : NNReal) : ℝ) W.carrier := by
    calc
      (slabProductBody A (thickBody rn W) (3 * rn) hslab).carrier
          ⊆ Metric.cthickening ((2 * (3 * rn) : NNReal) : ℝ) (thickBody rn W).carrier :=
        slabProductBody_subset_cthickening (thickBody rn W) hslab
      _ ⊆ Metric.cthickening ((8 * rn : NNReal) : ℝ) W.carrier := by
        rw [show (2 * (3 * rn : NNReal) : NNReal) = 6 * rn by ring]
        rw [show (thickBody rn W).carrier =
            Metric.cthickening ((2 * rn : NNReal) : ℝ) W.carrier by simp [thickBody]]
        have h8 : (8 * rn : NNReal) = 6 * rn + 2 * rn := by ring
        rw [h8]
        rw [NNReal.coe_add]
        exact Metric.cthickening_cthickening_subset (NNReal.coe_nonneg (6 * rn))
          (NNReal.coe_nonneg (2 * rn)) W.carrier
  -- Step 3: doubling bound `|N_{8rn}(W)| ≤ Θ(3,4)·|N_{2rn}(W)|`, since `8rn ≤ 4·(2rn)`.
  have hdoubling : volume (Metric.cthickening ((8 * rn : NNReal) : ℝ) W.carrier)
      ≤ (cthickeningDoublingConst (Module.finrank ℝ E) 4 : ENNReal) *
          volume (Metric.cthickening ((2 * rn : NNReal) : ℝ) W.carrier) := by
    refine volume_cthickening_le_doubling_mul W.convex W.nonempty (m := 4) ?hm ?hab
    · norm_num
    · exact le_of_eq (by ring)
  -- Assemble.
  calc
    2 * ((3 * rn : NNReal) : ENNReal) *
        volume ((thickBody rn W).orthogonalProjectionImage A).carrier
        = volume (slabProductBody A (thickBody rn W) (3 * rn) hslab).carrier := hPvol_eq.symm
    _ ≤ volume (Metric.cthickening ((8 * rn : NNReal) : ℝ) W.carrier) := measure_mono hsub
    _ ≤ (cthickeningDoublingConst (Module.finrank ℝ E) 4 : ENNReal) *
          volume (Metric.cthickening ((2 * rn : NNReal) : ℝ) W.carrier) := hdoubling
    _ = (projectionVolumeComparisonConst : ENNReal) * volume (thickBody rn W).carrier := by
      rw [hdim]
      rw [show (cthickeningDoublingConst 3 4 : ENNReal) =
          (projectionVolumeComparisonConst : ENNReal) by rfl]
      simp [thickBody]

omit [Nontrivial E] in
/-- The unconditional upper bound `|V| ≤ 6r|π(V)|` for a body inside the slab `N_{3r}(H)`. -/
private lemma volume_thickBody_le {A : AffineSubspace ℝ E} [Nonempty ↑A]
    (hcodim : Module.finrank ℝ E = Module.finrank ℝ A.direction + 1)
    (W : ConvexSpaceBody E) {rn : NNReal}
    (hslab : (thickBody rn W).carrier
      ⊆ Metric.cthickening ((3 * rn : NNReal) : ℝ) (A : Set E)) :
    volume (thickBody rn W).carrier
      ≤ 2 * ((3 * rn : NNReal) : ENNReal) *
        volume ((thickBody rn W).orthogonalProjectionImage A).carrier := by
  have hcarrier_eq : ((thickBody rn W).orthogonalProjectionImage A).carrier =
      orthogonalProjection A '' (thickBody rn W).carrier :=
    ConvexSpaceBody.coe_orthogonalProjectionImage (thickBody rn W) A
  rw [hcarrier_eq]
  exact volume_le_two_mul_volume_orthogonalProjection_image A hcodim (r := 3 * rn)
    (s := (thickBody rn W).carrier) hslab

/-- **Volume of the slab product body** (blueprint `lem:productBodyVolumeRatio`): the product body
over the shadow of `N_{2r}(K)` has volume at most `κ|K|`. It lies in `N_{8r}(K)`, and since `r` is
the shortest affine thickness of `K` we have `8r + τ_k(K) ≤ 9τ_k(K)` at every rank. -/
private lemma slabProductBody_volume_le {A : AffineSubspace ℝ E} [Nonempty ↑A]
    (hdim : Module.finrank ℝ E = 3) (K : ConvexSpaceBody E) {rn : NNReal}
    (hrn : (rn : ENNReal) ≤ Metric.ethickness.scale ℝ K.carrier)
    (hKt : (thickBody rn K).carrier
      ⊆ Metric.cthickening ((3 * rn : NNReal) : ℝ) (A : Set E)) :
    volume (slabProductBody A (thickBody rn K) (3 * rn) hKt).carrier
      ≤ (productBodyVolumeRatioConst : ENNReal) * volume K.carrier := by
  -- The product body lies in N_{2·(3rn)}(N_{2rn}(K.carrier)) ⊆ N_{8rn}(K.carrier).
  have hsub : (slabProductBody A (thickBody rn K) (3 * rn) hKt).carrier
      ⊆ Metric.cthickening ((8 * rn : NNReal) : ℝ) K.carrier := by
    calc
      (slabProductBody A (thickBody rn K) (3 * rn) hKt).carrier
          ⊆ Metric.cthickening ((2 * (3 * rn : NNReal) : NNReal) : ℝ)
              (thickBody rn K).carrier := by
            exact slabProductBody_subset_cthickening (A := A) (thickBody rn K) (ρ := 3 * rn) hKt
      _ ⊆ Metric.cthickening (((2 * (3 * rn : NNReal) : NNReal) : ℝ) +
              ((2 * rn : NNReal) : ℝ)) K.carrier := by
            rw [show (thickBody rn K).carrier =
                Metric.cthickening ((2 * rn : NNReal) : ℝ) K.carrier by simp [thickBody]]
            exact Metric.cthickening_cthickening_subset (NNReal.coe_nonneg _)
              (NNReal.coe_nonneg _) K.carrier
      _ = Metric.cthickening ((8 * rn : NNReal) : ℝ) K.carrier := by
            have hsum : (2 * (3 * rn : NNReal) : NNReal) + (2 * rn : NNReal) =
                (8 * rn : NNReal) := by
              ring
            rw [← hsum]
            rw [NNReal.coe_add]
  -- At every rank `k < 3`, `rn ≤ τ_k(K)` (since `rn ≤ scale` and `scale` is the minimum), so
  -- `8rn + τ_k(K) ≤ 9·τ_k(K)`.
  have ha : ∀ k ∈ Finset.range (Module.finrank ℝ E),
      ((8 * rn : NNReal) : ENNReal) + Metric.ethickness ℝ K.carrier k
        ≤ (9 : ENNReal) * Metric.ethickness ℝ K.carrier k := by
    intro k hk
    have hk' : k < Module.finrank ℝ E := Finset.mem_range.mp hk
    have hrnk : (rn : ENNReal) ≤ Metric.ethickness ℝ K.carrier k :=
      hrn.trans (Metric.ethickness.scale_le K.carrier hk')
    calc
      ((8 * rn : NNReal) : ENNReal) + Metric.ethickness ℝ K.carrier k
          = (8 : ENNReal) * (rn : ENNReal) + Metric.ethickness ℝ K.carrier k := by
            norm_num [ENNReal.coe_mul]
      _ ≤ (8 : ENNReal) * Metric.ethickness ℝ K.carrier k + Metric.ethickness ℝ K.carrier k := by
            gcongr
      _ = (9 : ENNReal) * Metric.ethickness ℝ K.carrier k := by
            ring
  -- Apply the volume-doubling bound at radius `8rn` and identify the constant.
  have hvol8 : volume (Metric.cthickening ((8 * rn : NNReal) : ℝ) K.carrier)
      ≤ (cthickeningDoublingConst (Module.finrank ℝ E) 9 : ENNReal) * volume K.carrier := by
    exact volume_cthickening_le_doubling_mul_volume K.convex (m := 9) (a := 8 * rn) ha
  calc
    volume (slabProductBody A (thickBody rn K) (3 * rn) hKt).carrier
        ≤ volume (Metric.cthickening ((8 * rn : NNReal) : ℝ) K.carrier) :=
          measure_mono hsub
    _ ≤ (cthickeningDoublingConst (Module.finrank ℝ E) 9 : ENNReal) * volume K.carrier := hvol8
    _ = (productBodyVolumeRatioConst : ENNReal) * volume K.carrier := by
          rw [productBodyVolumeRatioConst, hdim]

/-- **Frostman transfer to the thickened family in the product body** (blueprint
`lem:frostmanThickenedProduct`). The maximal density of the thickened family is controlled by that
of the original family up to the uniform thickening ratio `M`, and the density of the thickened
family in the product body is bounded below by the density of the original family in `K` divided by
the volume ratio `κ`; combining the two through `Δ_max` gives the Frostman property with constant
`M²·κ·C`. -/
private lemma frostman_thickened {C : ENNReal} {rn : NNReal}
    (hdim : Module.finrank ℝ E = 3)
    (K P : ConvexSpaceBody E)
    (hsub : ∀ i ∈ s, (V i).carrier ⊆ K.carrier)
    (hFr : ConvexSpaceBody.IsFrostmanIn s (fun i => (V i).toConvexSpaceBody) K C)
    (hne : s.Nonempty)
    (hVpos : ∀ i ∈ s, volume (V i).carrier ≠ 0)
    (hunif : ∀ i ∈ s, ∀ j ∈ s,
      Metric.thickness ℝ (V i).carrier ≤ 2 • Metric.thickness ℝ (V j).carrier)
    (hVtP : ∀ i ∈ s, thickBody rn (V i).toConvexSpaceBody ≤ P)
    (hP : volume P.carrier ≤ (productBodyVolumeRatioConst : ENNReal) * volume K.carrier) :
    ConvexSpaceBody.IsFrostmanIn s (fun i => thickBody rn (V i).toConvexSpaceBody) P
      ((thickeningRatioConst 3 : ENNReal) ^ 2 * (productBodyVolumeRatioConst : ENNReal) * C) := by
  set M : ENNReal := (thickeningRatioConst 3 : ENNReal) with hM_def
  set κ : ENNReal := (productBodyVolumeRatioConst : ENNReal) with hκ_def
  set Wt : ι → ConvexSpaceBody E := fun i => thickBody rn (V i).toConvexSpaceBody
  -- Bridge `hunif` from `Metric.thickness` to `Metric.ethickness`.
  have ethick_comp : ∀ i ∈ s, ∀ j ∈ s,
      Metric.ethickness ℝ (V i).carrier ≤ 2 • Metric.ethickness ℝ (V j).carrier := by
    intro i hi j hj
    have h := hunif i hi j hj
    simpa using (thickness_le_nsmul_thickness_iff (W := (V i).toConvexSpaceBody)
      (W' := (V j).toConvexSpaceBody) (a := 2)).mp h
  obtain ⟨i₀, hi₀⟩ := hne
  have hvoli₀ : volume (V i₀).carrier ≠ 0 := hVpos i₀ hi₀
  have hvoli₀top : volume (V i₀).carrier ≠ ⊤ := (V i₀).isCompact.measure_ne_top
  -- The uniform thickening-ratio inequalities: `b_i · a_{i₀} ≤ M · b_{i₀} · a_i` and the reverse.
  have hratio (i : ι) (hi : i ∈ s) :
      volume (Wt i).carrier * volume (V i₀).carrier
        ≤ M * volume (Wt i₀).carrier * volume (V i).carrier := by
    have hv := volume_cthickening_mul_volume_le (X := (V i).carrier) (Y := (V i₀).carrier)
      (V i).convex (V i).nonempty (V i₀).convex (V i₀).nonempty
      (ethick_comp i hi i₀ hi₀) (ethick_comp i₀ hi₀ i hi) (2 * rn)
    rw [hdim] at hv
    simpa [Wt, thickBody, M, mul_assoc, mul_comm, mul_left_comm] using hv
  have hratio₂ (i : ι) (hi : i ∈ s) :
      volume (V i).carrier * volume (Wt i₀).carrier
        ≤ M * volume (V i₀).carrier * volume (Wt i).carrier := by
    have hv := volume_cthickening_mul_volume_le (X := (V i₀).carrier) (Y := (V i).carrier)
      (V i₀).convex (V i₀).nonempty (V i).convex (V i).nonempty
      (ethick_comp i₀ hi₀ i hi) (ethick_comp i hi i₀ hi₀) (2 * rn)
    rw [hdim] at hv
    simpa [Wt, thickBody, M, mul_assoc, mul_comm, mul_left_comm] using hv
  -- `|K| ≠ 0` since some `V i₀ ⊆ K` has positive volume.
  have hKvol0 : volume K.carrier ≠ 0 := by
    intro hK0
    exact hVpos i₀ hi₀ (measure_mono_null (hsub i₀ hi₀) hK0)
  have hKvoltop : volume K.carrier ≠ ⊤ := K.isCompact.measure_ne_top
  -- `b_{i₀} · Δ(𝒱, W) ≤ M · a_{i₀} · κ · Δ(𝒱̃, P)`.
  have hstep2 : volume (Wt i₀).carrier * Kakeya.densityIn s (fun i => (V i).toConvexSpaceBody) K
      ≤ M * volume (V i₀).carrier * κ * Kakeya.densityIn s Wt P := by
    have hmain : (volume (Wt i₀).carrier *
          Kakeya.densityIn s (fun i => (V i).toConvexSpaceBody) K) * volume K.carrier
        ≤ (M * volume (V i₀).carrier * κ * Kakeya.densityIn s Wt P) * volume K.carrier := by
      calc
        (volume (Wt i₀).carrier * Kakeya.densityIn s (fun i => (V i).toConvexSpaceBody) K) *
            volume K.carrier
            = volume (Wt i₀).carrier *
                (Kakeya.densityIn s (fun i => (V i).toConvexSpaceBody) K * volume K.carrier) := by
              rw [mul_assoc]
        _ = volume (Wt i₀).carrier * (∑ i ∈ s, volume (V i).carrier) := by
              rw [Kakeya.sum_volume_eq_densityIn_mul_volume' hsub]
        _ = ∑ i ∈ s, volume (Wt i₀).carrier * volume (V i).carrier := by
              rw [Finset.mul_sum]
        _ = ∑ i ∈ s, volume (V i).carrier * volume (Wt i₀).carrier := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [mul_comm]
        _ ≤ ∑ i ∈ s, M * volume (V i₀).carrier * volume (Wt i).carrier := by
              refine Finset.sum_le_sum ?_
              intro i hi
              exact hratio₂ i hi
        _ = M * volume (V i₀).carrier * (∑ i ∈ s, volume (Wt i).carrier) := by
              rw [Finset.mul_sum]
        _ = M * volume (V i₀).carrier * (Kakeya.densityIn s Wt P * volume P.carrier) := by
              rw [Kakeya.sum_volume_eq_densityIn_mul_volume' hVtP]
        _ = (M * volume (V i₀).carrier * Kakeya.densityIn s Wt P) * volume P.carrier := by
              ring
        _ ≤ (M * volume (V i₀).carrier * Kakeya.densityIn s Wt P) * (κ * volume K.carrier) := by
              gcongr
        _ = (M * volume (V i₀).carrier * κ * Kakeya.densityIn s Wt P) * volume K.carrier := by
              ring
    exact (ENNReal.mul_le_mul_iff_left hKvol0 hKvoltop).mp hmain
  -- Frostman transfer, via `maxDensity_le_of_forall_sum_le`.
  apply ConvexSpaceBody.IsFrostmanIn.of_maxDensity_le
  apply Kakeya.maxDensity_le_of_forall_sum_le
  intro Q
  -- Step 1: `a_{i₀} · ∑_{𝒱̃ ≤ Q} b_i ≤ M · b_{i₀} · C · Δ(𝒱, W) · |Q|`.
  have hstep1 : volume (V i₀).carrier * (∑ i ∈ s with Wt i ≤ Q, volume (Wt i).carrier)
      ≤ M * volume (Wt i₀).carrier * C *
          Kakeya.densityIn s (fun i => (V i).toConvexSpaceBody) K * volume Q.carrier := by
    have hsubset : {i ∈ s | Wt i ≤ Q} ⊆
        {i ∈ s | (V i).toConvexSpaceBody ≤ Q} := by
      intro i hi
      rw [Finset.mem_filter] at hi ⊢
      refine ⟨hi.1, le_trans ?_ hi.2⟩
      simpa [Wt, thickBody] using
        (ConvexSpaceBody.self_le_cthickening (V i).toConvexSpaceBody ((2 * rn : NNReal) : ℝ))
    calc
      volume (V i₀).carrier * (∑ i ∈ s with Wt i ≤ Q, volume (Wt i).carrier)
          = ∑ i ∈ s with Wt i ≤ Q, volume (V i₀).carrier * volume (Wt i).carrier := by
            rw [Finset.mul_sum]
      _ = ∑ i ∈ s with Wt i ≤ Q, volume (Wt i).carrier * volume (V i₀).carrier := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [mul_comm]
      _ ≤ ∑ i ∈ s with Wt i ≤ Q, M * volume (Wt i₀).carrier * volume (V i).carrier := by
            refine Finset.sum_le_sum ?_
            intro i hi
            exact hratio i (Finset.mem_filter.mp hi).1
      _ = M * volume (Wt i₀).carrier *
          (∑ i ∈ s with Wt i ≤ Q, volume (V i).carrier) := by
            rw [Finset.mul_sum]
      _ ≤ M * volume (Wt i₀).carrier *
          (∑ i ∈ s with (V i).toConvexSpaceBody ≤ Q, volume (V i).carrier) := by
            exact mul_le_mul_right (Finset.sum_le_sum_of_subset hsubset)
              (M * volume (Wt i₀).carrier)
      _ ≤ M * volume (Wt i₀).carrier *
          (Kakeya.maxDensity s (fun i => (V i).toConvexSpaceBody) * volume Q.carrier) := by
            exact mul_le_mul_right
              (Kakeya.sum_volume_le_maxDensity_mul_volume s (fun i => (V i).toConvexSpaceBody) Q)
              (M * volume (Wt i₀).carrier)
      _ ≤ M * volume (Wt i₀).carrier *
          ((C * Kakeya.densityIn s (fun i => (V i).toConvexSpaceBody) K) * volume Q.carrier) := by
            exact mul_le_mul_right
              (mul_le_mul_left (hFr.maxDensity_le_of_carrier_subset hsub) (volume Q.carrier))
              (M * volume (Wt i₀).carrier)
      _ = M * volume (Wt i₀).carrier * C *
            Kakeya.densityIn s (fun i => (V i).toConvexSpaceBody) K * volume Q.carrier := by
            ring
  -- Combine Steps 1 and 2 and cancel `a_{i₀}`.
  have hcombined : volume (V i₀).carrier * (∑ i ∈ s with Wt i ≤ Q, volume (Wt i).carrier)
      ≤ volume (V i₀).carrier * ((M ^ 2 * κ * C) * Kakeya.densityIn s Wt P * volume Q.carrier) := by
    calc
      volume (V i₀).carrier * (∑ i ∈ s with Wt i ≤ Q, volume (Wt i).carrier)
          ≤ M * volume (Wt i₀).carrier * C *
              Kakeya.densityIn s (fun i => (V i).toConvexSpaceBody) K * volume Q.carrier := hstep1
      _ = (volume (Wt i₀).carrier * Kakeya.densityIn s (fun i => (V i).toConvexSpaceBody) K) *
            (M * C * volume Q.carrier) := by
            ring
      _ ≤ (M * volume (V i₀).carrier * κ * Kakeya.densityIn s Wt P) *
          (M * C * volume Q.carrier) := by
            exact mul_le_mul hstep2 (le_refl _) (by simp) (by simp)
      _ = volume (V i₀).carrier *
          ((M ^ 2 * κ * C) * Kakeya.densityIn s Wt P * volume Q.carrier) := by
            ring
  exact (ENNReal.mul_le_mul_iff_right hvoli₀ hvoli₀top).mp hcombined

/-- **Shading proportion of the projected family** (blueprint `lem:projectedProportion`): the
shadow of the `r/2`-thickened shading occupies at least `c_th·λ₀·D⁻²` of the shadow of the
`2r`-thickened body. -/
private lemma cordoba_hfull {A : AffineSubspace ℝ E} [Nonempty ↑A]
    (hdim : Module.finrank ℝ E = 3)
    (hcodim : Module.finrank ℝ E = Module.finrank ℝ A.direction + 1)
    {lam : ENNReal} {rn : NNReal} (hrn : rn ≠ 0) (S : ShadedBody E)
    (hVpos : volume S.carrier ≠ 0)
    (hlam : lam * volume S.carrier ≤ volume S.shade)
    (hslabY : Metric.cthickening ((rn / 2 : NNReal) : ℝ) S.shade
      ⊆ Metric.cthickening ((3 * rn : NNReal) : ℝ) (A : Set E))
    (hslab : (thickBody rn S.toConvexSpaceBody).carrier
      ⊆ Metric.cthickening ((3 * rn : NNReal) : ℝ) (A : Set E)) :
    (IsConvexSet.volume_cthickening_ge_of_volume_ge.c 3 : ENNReal) * lam
          * (projectionVolumeComparisonConst : ENNReal)⁻¹
          * (projectionVolumeComparisonConst : ENNReal)⁻¹
        * volume
          ((thickShaded rn S).orthogonalProjectionImage A
            (isClosed_thickShaded_shade rn S)).carrier
      ≤ volume
          ((thickShaded rn S).orthogonalProjectionImage A
            (isClosed_thickShaded_shade rn S)).shade := by
  set cth : ENNReal := (IsConvexSet.volume_cthickening_ge_of_volume_ge.c 3 : ENNReal)
  set D : ENNReal := (projectionVolumeComparisonConst : ENNReal)
  set a : ENNReal := 2 * ((3 * rn : NNReal) : ENNReal)
  set X : ShadedBody ↑A :=
    (thickShaded rn S).orthogonalProjectionImage A (isClosed_thickShaded_shade rn S)
  set volBody : ENNReal := volume (thickBody rn S.toConvexSpaceBody).carrier
  set volHalf : ENNReal := volume (Metric.cthickening ((rn / 2 : NNReal) : ℝ) S.carrier)
  set volYhalf : ENNReal := volume (Metric.cthickening ((rn / 2 : NNReal) : ℝ) S.shade)
  -- Nonzeroness of the constants appearing in the proof.
  have hD0 : D ≠ 0 := by
    refine ENNReal.coe_ne_zero.mpr ?_
    simp [projectionVolumeComparisonConst, cthickeningDoublingConst,
      Metric.lt_volume_convexHull.c, Nat.factorial]
  have ha0 : a ≠ 0 :=
    mul_ne_zero (by norm_num : (2 : ENNReal) ≠ 0)
      (ENNReal.coe_ne_zero.mpr (mul_ne_zero (by norm_num : (3 : NNReal) ≠ 0) hrn))
  have hatop : a ≠ ⊤ := ENNReal.mul_ne_top (by norm_num : (2 : ENNReal) ≠ ⊤) ENNReal.coe_ne_top
  have hDinvcancel : D⁻¹ * D = 1 := ENNReal.inv_mul_cancel hD0 ENNReal.coe_ne_top
  -- (i) Reverse projection comparison for the `2r`-thickened carrier: `a·|π(N₂V)| ≤ D·|N₂V|`.
  have hrev : a * volume X.carrier ≤ D * volBody :=
    revProj hdim hcodim S.toConvexSpaceBody hslab
  -- (ii) Doubling `|N_{2r}(V)| ≤ D·|N_{r/2}(V)|` via
  -- `volume_cthickening_le_doubling_mul` with `m = 4`.
  have hdoubling : volBody ≤ D * volHalf := by
    have hb := volume_cthickening_le_doubling_mul (X := S.carrier) S.toConvexSpaceBody.convex
      S.toConvexSpaceBody.nonempty (m := 4) (by norm_num : (1 : ℕ) ≤ 4) (a := 2 * rn)
      (b := rn / 2) (le_of_eq (by ring))
    rw [hdim] at hb
    exact hb
  -- (iii) Joint-thickening shading estimate at scale `r/2`: `c_th·lam·|N_{r/2}V| ≤ |N_{r/2}Y|`.
  have hfull : cth * lam * volHalf ≤ volYhalf := by
    have hb := IsConvexSet.volume_cthickening_ge_of_volume_ge (V := S.carrier) (Y := S.shade)
      S.toConvexSpaceBody.isConvexSet S.toConvexSpaceBody.isCompact.isBounded
      (pos_iff_ne_zero.mpr hVpos) S.shade_subset (rn / 2) (a := lam) hlam
    rw [hdim] at hb
    exact hb
  -- (iv) Unconditional slab bound for the `r/2`-thickened shade: `|N_{r/2}Y| ≤ a·|π(N_{r/2}Y)|`.
  have hslabbound : volYhalf ≤ a * volume X.shade :=
    volume_le_two_mul_volume_orthogonalProjection_image A hcodim
      (r := 3 * rn) (s := Metric.cthickening ((rn / 2 : NNReal) : ℝ) S.shade) hslabY
  -- Chain the four estimates and cancel the fibre factor `a`.
  have hmain : a * (cth * lam * D⁻¹ * D⁻¹ * volume X.carrier) ≤ a * volume X.shade := by
    calc
      a * (cth * lam * D⁻¹ * D⁻¹ * volume X.carrier)
          = cth * lam * D⁻¹ * D⁻¹ * (a * volume X.carrier) := by ring
      _ ≤ cth * lam * D⁻¹ * D⁻¹ * (D * (D * volHalf)) :=
            mul_le_mul_right (hrev.trans (mul_le_mul_right hdoubling D)) _
      _ = cth * lam * volHalf * (D⁻¹ * D) * (D⁻¹ * D) := by ring
      _ = cth * lam * volHalf := by rw [hDinvcancel, mul_one, mul_one]
      _ ≤ volYhalf := hfull
      _ ≤ a * volume X.shade := hslabbound
  exact (ENNReal.mul_le_mul_iff_right ha0 hatop).mp hmain

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **Affine-thickness comparability of the shadows** (blueprint `lem:projectedThicknessUniform`):
the shadows of the `2r`-thickened bodies have pairwise comparable affine thicknesses. Both the
upper bound `2r + τ_k(V_i)` and the lower bound `2r + τ_k(π V_j)` are available, and the slab
bound `τ_k(V_j) ≤ r + τ_k(π V_j)` closes the gap with the factor `2` exactly. -/
private lemma cordoba_hunif {A : AffineSubspace ℝ E} [Nonempty ↑A]
    (hAdim : Module.finrank ℝ A.direction = 2)
    {rn : NNReal} (W W' : ConvexSpaceBody E)
    (hW' : W'.carrier ⊆ Metric.cthickening (rn : ℝ) (A : Set E))
    (hunif : Metric.thickness ℝ W.carrier ≤ 2 • Metric.thickness ℝ W'.carrier) :
    Metric.thickness ℝ ((thickBody rn W).orthogonalProjectionImage A).carrier
      ≤ 2 • Metric.thickness ℝ ((thickBody rn W').orthogonalProjectionImage A).carrier := by
  -- Pass to `ethickness` through the bridge (both sides are carriers of convex bodies).
  have heth_unif : Metric.ethickness ℝ W.carrier ≤ 2 • Metric.ethickness ℝ W'.carrier :=
    (thickness_le_nsmul_thickness_iff (W := W) (W' := W') (a := 2)).mp hunif
  -- Prove the `ethickness`-level comparability of the shadows, pointwise in the rank `k`. The
  -- carriers of the projected bodies are definitionally the projected carrier sets.
  have heth_goal : Metric.ethickness ℝ (orthogonalProjection A '' (thickBody rn W).carrier) ≤
      2 • Metric.ethickness ℝ (orthogonalProjection A '' (thickBody rn W').carrier) := by
    rw [Pi.le_def]
    intro k
    rw [Pi.smul_apply, nsmul_eq_mul]
    by_cases hk : k < Module.finrank ℝ A.direction
    · calc
        Metric.ethickness ℝ (orthogonalProjection A '' (thickBody rn W).carrier) k
            ≤ Metric.ethickness ℝ (thickBody rn W).carrier k :=
              ethickness_image_orthogonalProjection_le (A := A) (thickBody rn W).carrier k
        _ = Metric.ethickness ℝ (Metric.cthickening ((2 * rn : NNReal) : ℝ) W.carrier) k := rfl
        _ ≤ ((2 * rn : NNReal) : ENNReal) + Metric.ethickness ℝ W.carrier k :=
              Metric.ethickness_cthickening_le ((2 * rn : NNReal)) k
        _ ≤ ((2 * rn : NNReal) : ENNReal) + 2 * Metric.ethickness ℝ W'.carrier k :=
              add_le_add_right
                (by simpa only [Pi.smul_apply, nsmul_eq_mul, Nat.cast_ofNat] using heth_unif k) _
        _ ≤ ((2 * rn : NNReal) : ENNReal) +
              2 * ((rn : ENNReal) +
                Metric.ethickness ℝ (orthogonalProjection A '' W'.carrier) k) :=
              add_le_add_right (mul_le_mul_right
                (ethickness_le_add_ethickness_image_orthogonalProjection hW' k) 2) _
        _ = 2 * (((2 * rn : NNReal) : ENNReal) +
              Metric.ethickness ℝ (orthogonalProjection A '' W'.carrier) k) := by
              push_cast
              ring
        _ ≤ 2 * Metric.ethickness ℝ
              (orthogonalProjection A ''
                Metric.cthickening ((2 * rn : NNReal) : ℝ) W'.carrier) k :=
              mul_le_mul_right (le_ethickness_image_orthogonalProjection_cthickening
                (X := W'.carrier) W'.isCompact' W'.nonempty (t := 2 * rn) hk) 2
        _ = 2 * Metric.ethickness ℝ (orthogonalProjection A '' (thickBody rn W').carrier) k := rfl
    · -- For ranks at least the ambient dimension of the shadow, both sides vanish.
      have hzero : ∀ t : Set ↑A, Metric.ethickness ℝ t k = 0 := fun _ =>
        Metric.ethickness_eq_zero_of_finrank_le (V := A.direction) (by omega)
      rw [hzero, hzero, mul_zero]
  -- Convert back to `thickness`: take `toReal` of the pointwise `ethickness` inequality. The
  -- projected carriers are bounded (compact convex bodies), so `toReal_ethickness` applies.
  have hbX : Bornology.IsBounded (orthogonalProjection A '' (thickBody rn W).carrier) :=
    ((thickBody rn W).orthogonalProjectionImage A).isBounded
  have hbY : Bornology.IsBounded (orthogonalProjection A '' (thickBody rn W').carrier) :=
    ((thickBody rn W').orthogonalProjectionImage A).isBounded
  change Metric.thickness ℝ (orthogonalProjection A '' (thickBody rn W).carrier) ≤
    2 • Metric.thickness ℝ (orthogonalProjection A '' (thickBody rn W').carrier)
  intro k
  rw [Pi.smul_apply, nsmul_eq_mul]
  calc
    Metric.thickness ℝ (orthogonalProjection A '' (thickBody rn W).carrier) k
        = (Metric.ethickness ℝ (orthogonalProjection A '' (thickBody rn W).carrier) k).toReal :=
          (Metric.toReal_ethickness (V := A.direction) hbX k).symm
    _ ≤ (2 * Metric.ethickness ℝ
          (orthogonalProjection A '' (thickBody rn W').carrier) k).toReal :=
          ENNReal.toReal_mono
            (ENNReal.mul_ne_top (by norm_num)
              (Metric.ethickness_ne_top (V := A.direction) hbY k))
            (by simpa only [Pi.smul_apply, nsmul_eq_mul, Nat.cast_ofNat] using heth_goal k)
    _ = (2 : ℝ) * Metric.thickness ℝ (orthogonalProjection A '' (thickBody rn W').carrier) k := by
          rw [ENNReal.toReal_mul, Metric.toReal_ethickness (V := A.direction) hbY k]
          norm_num

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **Eccentricity transfer to the shadows** (blueprint `lem:projectedEccentricity`): the shadow
eccentricity exponent is `N + 16`, the shift absorbing the product-body volume ratio
`κ ≤ 2^16`. -/
private lemma ecc_transfer {volP volKp volK volW volQ : ENNReal} {N : ℕ} {rn : NNReal}
    (hrn : rn ≠ 0)
    (hPKp : volP = 2 * ((3 * rn : NNReal) : ENNReal) * volKp)
    (hPK : volP ≤ (productBodyVolumeRatioConst : ENNReal) * volK)
    (hKW : volK ≤ 2 ^ N * volW)
    (hWQ : volW ≤ 2 * ((3 * rn : NNReal) : ENNReal) * volQ) :
    volKp ≤ 2 ^ (N + 16) * volQ := by
  set a : ENNReal := ((3 * rn : NNReal) : ENNReal)
  set κ : ENNReal := (productBodyVolumeRatioConst : ENNReal)
  have ha0 : a ≠ 0 := by
    exact ENNReal.coe_ne_zero.mpr (show (3 * rn : NNReal) ≠ 0 from
      mul_ne_zero (by norm_num : (3 : NNReal) ≠ 0) hrn)
  have hatop : a ≠ ⊤ := ENNReal.coe_ne_top
  have hfac0 : 2 * a ≠ 0 := mul_ne_zero (by norm_num : (2 : ENNReal) ≠ 0) ha0
  have hfactop : 2 * a ≠ ⊤ := ENNReal.mul_ne_top (by norm_num : (2 : ENNReal) ≠ ⊤) hatop
  have hκ : κ ≤ (2 ^ 16 : ENNReal) := by
    change (productBodyVolumeRatioConst : ENNReal) ≤ (2 ^ 16 : ENNReal)
    exact ENNReal.coe_le_coe.mpr (show productBodyVolumeRatioConst ≤ 2 ^ 16 from by
      rw [productBodyVolumeRatioConst, cthickeningDoublingConst]
      norm_num [Metric.lt_volume_convexHull.c, Nat.factorial])
  have hmain : volKp ≤ κ * 2 ^ N * volQ := by
    have hchain : 2 * a * volKp ≤ 2 * a * (κ * 2 ^ N * volQ) := by
      calc
        2 * a * volKp = volP := by rw [hPKp]
        _ ≤ κ * volK := hPK
        _ ≤ κ * (2 ^ N * volW) := by
          exact mul_le_mul_right hKW _
        _ ≤ κ * (2 ^ N * (2 * a * volQ)) := by
          exact mul_le_mul_right (mul_le_mul_right hWQ (2 ^ N)) _
        _ = 2 * a * (κ * 2 ^ N * volQ) := by
          ring
    exact (ENNReal.mul_le_mul_iff_right hfac0 hfactop).mp hchain
  calc
    volKp ≤ κ * 2 ^ N * volQ := hmain
    _ ≤ (2 ^ 16 * 2 ^ N) * volQ := by
      exact mul_le_mul_left (mul_le_mul' hκ le_rfl) volQ
    _ = 2 ^ (N + 16) * volQ := by
      rw [← pow_add]
      rw [Nat.add_comm]

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- Positivity of the shadow volume: it is nonzero because the body's volume is. -/
private lemma pos_of_le_two_mul {volW volQ : ENNReal} {rn : NNReal} (hW : volW ≠ 0)
    (hWQ : volW ≤ 2 * ((3 * rn : NNReal) : ENNReal) * volQ) : 0 < volQ := by
  by_contra hQ
  have hvolQ0 : volQ = 0 := le_antisymm (le_of_not_gt hQ) bot_le
  have hWle : volW ≤ 0 := by
    rw [hvolQ0] at hWQ
    simpa using hWQ
  exact hW (le_antisymm hWle bot_le)

/-- Cordoba bound for the projected family: an application of the affine planar Cordoba estimate
`le_volume_biUnion_TwoDim_affineSubspace` to the shadows of the `2r`-thickened family inside the
shadow of the slab product body, at the projected shading proportion `c_th·lam·D⁻²`, Frostman
constant `D·(M²·κ·C)` and eccentricity exponent `N + 16`. -/
private lemma cordoba_proj_le_of_thickenedFrostmanInProduct
    {A : AffineSubspace ℝ E} [Nonempty ↑A]
    (K : ConvexSpaceBody E) {C lam : ENNReal} {N : ℕ} {rn : NNReal}
    (hdim : Module.finrank ℝ E = 3)
    (hAdim : Module.finrank ℝ A.direction = 2)
    (hcodim : Module.finrank ℝ E = Module.finrank ℝ A.direction + 1)
    (hrn : rn ≠ 0)
    (hrnscale : (rn : ENNReal) ≤ Metric.ethickness.scale ℝ K.carrier)
    (hAsub : K.carrier ⊆ Metric.cthickening (rn : ℝ) (A : Set E))
    (hKt : (thickBody rn K).carrier
      ⊆ Metric.cthickening ((3 * rn : NNReal) : ℝ) (A : Set E))
    (hsub : ∀ i ∈ s, (V i).carrier ⊆ K.carrier)
    (hFroP : ConvexSpaceBody.IsFrostmanIn s
      (fun i => thickBody rn (V i).toConvexSpaceBody)
      (slabProductBody A (thickBody rn K) (3 * rn) hKt)
      ((1 + (thickeningRatioConst 3 : ENNReal) ^ 2) *
        (productBodyVolumeRatioConst : ENNReal) * C))
    (hne : s.Nonempty)
    (hVpos : ∀ i ∈ s, volume (V i).carrier ≠ 0)
    (hlam : lam * (∑ i ∈ s, volume (V i).carrier) ≤
      ∑ i ∈ s, volume (V i).shade)
    (hunif : ∀ i ∈ s, ∀ j ∈ s,
      Metric.thickness ℝ (V i).carrier ≤ 2 • Metric.thickness ℝ (V j).carrier)
    (hN : ∀ i ∈ s, volume K.carrier ≤ 2 ^ N * volume (V i).carrier) :
    (ConvexSpaceBody.IsFrostmanIn.le_volume_biUnion_TwoDim.c : ENNReal) *
        ((aggregateProjectionWeightConst : ENNReal)⁻¹ *
          (IsConvexSet.volume_cthickening_ge_of_volume_ge.c 3 : ENNReal) * lam
          * (projectionVolumeComparisonConst : ENNReal)⁻¹
          * (projectionVolumeComparisonConst : ENNReal)⁻¹) ^ 2 *
        volume ((slabProductBody A (thickBody rn K) (3 * rn) hKt).orthogonalProjectionImage
          A).carrier
      ≤ (((N + 16 : ℕ) : ENNReal) + 1) *
          ((projectionVolumeComparisonConst : ENNReal) *
            ((1 + (thickeningRatioConst 3 : ENNReal) ^ 2) *
              (productBodyVolumeRatioConst : ENNReal) * C)) *
          volume (⋃ i ∈ s,
            ((thickShaded rn (V i)).orthogonalProjectionImage A
              (isClosed_thickShaded_shade rn (V i))).shade) := by
  haveI : Fact (Module.finrank ℝ A.direction = 2) := ⟨hAdim⟩
  let P : ConvexSpaceBody E := slabProductBody A (thickBody rn K) (3 * rn) hKt
  let Vproj : ι → ShadedBody ↑A := fun i =>
    (thickShaded rn (V i)).orthogonalProjectionImage A (isClosed_thickShaded_shade rn (V i))
  let Kproj : ConvexSpaceBody ↑A := P.orthogonalProjectionImage A
  let μ : ENNReal := (aggregateProjectionWeightConst : ENNReal)⁻¹ *
    (IsConvexSet.volume_cthickening_ge_of_volume_ge.c 3 : ENNReal) * lam *
    (projectionVolumeComparisonConst : ENNReal)⁻¹ * (projectionVolumeComparisonConst : ENNReal)⁻¹
  let Cproj : ENNReal := (projectionVolumeComparisonConst : ENNReal) *
    ((1 + (thickeningRatioConst 3 : ENNReal) ^ 2) *
      (productBodyVolumeRatioConst : ENNReal) * C)
  -- Each thickened inner body lies in the slab `N_{3r}(A)`.
  have hslab_i : ∀ i ∈ s, (thickBody rn (V i).toConvexSpaceBody).carrier
      ⊆ Metric.cthickening ((3 * rn : NNReal) : ℝ) (A : Set E) := by
    intro i hi
    rw [show (3 * rn : NNReal) = 2 * rn + rn by ring]
    exact cthickening_subset_cthickening_affineSubspace (A := A) (X := (V i).carrier)
      (a := 2 * rn) (b := rn) ((hsub i hi).trans hAsub)
  -- The `r/2`-thickened shading of each body also lies in the slab.
  have hslabY_i : ∀ i ∈ s,
      Metric.cthickening ((rn / 2 : NNReal) : ℝ) (V i).shade
        ⊆ Metric.cthickening ((3 * rn : NNReal) : ℝ) (A : Set E) := by
    intro i hi
    refine (cthickening_subset_cthickening_affineSubspace (A := A) (X := (V i).shade)
      (a := rn / 2) (b := rn)
      ((V i).shade_subset.trans ((hsub i hi).trans hAsub))).trans
      (Metric.cthickening_mono ?_ (A : Set E))
    push_cast
    linarith [NNReal.coe_nonneg rn]
  -- Thickened bodies are contained in the product body.
  have hVtP : ∀ i ∈ s, thickBody rn (V i).toConvexSpaceBody ≤ P := by
    intro i hi
    have hthick_sub :
        (thickBody rn (V i).toConvexSpaceBody).carrier ⊆ (thickBody rn K).carrier :=
      Metric.cthickening_subset_of_subset ((2 * rn : NNReal) : ℝ) (hsub i hi)
    rw [SetLike.le_def]
    exact fun x hx =>
      ⟨Set.mem_image_of_mem (orthogonalProjection A) (hthick_sub hx), hslab_i i hi hx⟩
  -- Volume bound for the product body.
  have hP : volume P.carrier ≤ (productBodyVolumeRatioConst : ENNReal) * volume K.carrier :=
    slabProductBody_volume_le (A := A) hdim K hrnscale hKt
  -- Reverse projection comparison for each thickened body.
  have hvolume_i : ∀ i ∈ s,
      2 * ((3 * rn : NNReal) : ENNReal) *
          volume ((thickBody rn (V i).toConvexSpaceBody).orthogonalProjectionImage A).carrier
        ≤ (projectionVolumeComparisonConst : ENNReal) *
            volume (thickBody rn (V i).toConvexSpaceBody).carrier :=
    fun i hi => revProj (A := A) hdim hcodim (V i).toConvexSpaceBody (hslab := hslab_i i hi)
  -- Frostman property of the projected family.
  have hFroProj : ConvexSpaceBody.IsFrostmanIn s
      (fun i => (thickBody rn (V i).toConvexSpaceBody).orthogonalProjectionImage A)
      (P.orthogonalProjectionImage A)
      ((projectionVolumeComparisonConst : ENNReal) *
        ((1 + (thickeningRatioConst 3 : ENNReal) ^ 2) *
          (productBodyVolumeRatioConst : ENNReal) * C)) := by
    have hr3 : 0 < (3 * rn : NNReal) :=
      mul_pos (by norm_num : 0 < (3 : NNReal)) (pos_iff_ne_zero.mpr hrn)
    exact ConvexSpaceBody.IsFrostmanIn.image_orthogonalProjection s A hcodim
      (fun i => thickBody rn (V i).toConvexSpaceBody) P (r := 3 * rn) hr3
      (C := (1 + (thickeningRatioConst 3 : ENNReal) ^ 2) *
        (productBodyVolumeRatioConst : ENNReal) * C)
      (D := projectionVolumeComparisonConst)
      hslab_i (slabProductBody_product (thickBody rn K) hKt)
      hvolume_i hFroP
  -- The product body volume identity `|P| = 6r|π(P)|`.
  have hKproj_carrier : Kproj.carrier = ((thickBody rn K).orthogonalProjectionImage A).carrier := by
    calc
      Kproj.carrier = orthogonalProjection A '' P.carrier :=
        ConvexSpaceBody.coe_orthogonalProjectionImage P A
      _ = orthogonalProjection A '' (thickBody rn K).carrier :=
        image_slabProductBody (thickBody rn K) hKt
      _ = ((thickBody rn K).orthogonalProjectionImage A).carrier :=
        (ConvexSpaceBody.coe_orthogonalProjectionImage (thickBody rn K) A).symm
  have hPKp : volume P.carrier =
      2 * ((3 * rn : NNReal) : ENNReal) * volume Kproj.carrier := by
    rw [hKproj_carrier,
      show P.carrier = (orthogonalProjection A ⁻¹'
          ((thickBody rn K).orthogonalProjectionImage A).carrier) ∩
        Metric.cthickening ((3 * rn : NNReal) : ℝ) (A : Set E) from rfl]
    exact volume_preimage_orthogonalProjection_inter_cthickening A hcodim
      ((thickBody rn K).orthogonalProjectionImage A) (3 * rn)
  -- Volume monotonicity under thickening.
  have hVi_le_thick : ∀ i ∈ s,
      volume (V i).carrier ≤ volume (thickBody rn (V i).toConvexSpaceBody).carrier :=
    fun i _ => measure_mono (SetLike.coe_subset_coe.mpr
      (ConvexSpaceBody.self_le_cthickening (V i).toConvexSpaceBody ((2 * rn : NNReal) : ℝ)))
  -- Eccentricity hypothesis for the projected family.
  have hKW : ∀ i ∈ s,
      volume K.carrier ≤ 2 ^ N * volume (thickBody rn (V i).toConvexSpaceBody).carrier :=
    fun i hi => (hN i hi).trans (mul_le_mul_right (hVi_le_thick i hi) (2 ^ N))
  -- Upper bound on the volume of a thickened body by its shadow.
  have hWQ : ∀ i ∈ s,
      volume (thickBody rn (V i).toConvexSpaceBody).carrier ≤
        2 * ((3 * rn : NNReal) : ENNReal) * volume (Vproj i).carrier :=
    fun i hi => volume_thickBody_le (A := A) hcodim (V i).toConvexSpaceBody (hslab := hslab_i i hi)
  -- Assemble the eccentricity transfer.
  have hN' : ∀ i ∈ s, volume Kproj.carrier ≤ 2 ^ (N + 16) * volume (Vproj i).carrier :=
    fun i hi => ecc_transfer (rn := rn) hrn hPKp hP (hKW i hi) (hWQ i hi)
  -- Positive shadow volume.
  have hvol' : ∀ i ∈ s, 0 < volume (Vproj i).carrier := fun i hi =>
    pos_of_le_two_mul (rn := rn)
      (ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.mpr (hVpos i hi)) (hVi_le_thick i hi)))
      (hWQ i hi)
  -- Containment of the projected family in the projected product body.
  have hsub' : ∀ i ∈ s, (Vproj i).carrier ⊆ Kproj.carrier := by
    intro i hi
    calc
      (Vproj i).carrier
          = orthogonalProjection A '' (thickBody rn (V i).toConvexSpaceBody).carrier :=
        ConvexSpaceBody.coe_orthogonalProjectionImage (thickBody rn (V i).toConvexSpaceBody) A
      _ ⊆ orthogonalProjection A '' P.carrier :=
        Set.image_mono (SetLike.coe_subset_coe.mpr (hVtP i hi))
      _ = Kproj.carrier := (ConvexSpaceBody.coe_orthogonalProjectionImage P A).symm
  -- Comparability of the projected affine thicknesses.
  have hunif' : ∀ i ∈ s, ∀ j ∈ s,
      Metric.thickness ℝ (Vproj i).carrier ≤ 2 • Metric.thickness ℝ (Vproj j).carrier :=
    fun i hi j hj => cordoba_hunif (A := A) hAdim (W := (V i).toConvexSpaceBody)
      (W' := (V j).toConvexSpaceBody) ((hsub j hj).trans hAsub) (hunif i hi j hj)
  -- Transfer the aggregate density from the original three-dimensional carriers to the
  -- two-dimensional projected carriers.  The transfer is division-free until the final
  -- cancellation of the explicit positive constant `R`.
  let a : ι → ENNReal := fun i ↦ volume (V i).carrier
  let b : ι → ENNReal := fun i ↦ volume (Vproj i).carrier
  let q : ι → ENNReal := fun i ↦ volume (V i).shade / volume (V i).carrier
  let R : ENNReal := aggregateProjectionWeightConst
  have hA0 : (∑ i ∈ s, a i) ≠ 0 := by
    obtain ⟨i, hi⟩ := hne
    exact ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.mpr (hVpos i hi)) (by
      simpa only [a] using
        (Finset.single_le_sum (f := fun i ↦ volume (V i).carrier)
          (fun _ _ ↦ bot_le) hi)))
  have hAtop : (∑ i ∈ s, a i) ≠ ⊤ := by
    exact ENNReal.sum_ne_top.2 fun i hi ↦ by
      change volume (V i).carrier ≠ ⊤
      exact (V i).isCompact.measure_ne_top
  have havg : lam * (∑ i ∈ s, a i) ≤ ∑ i ∈ s, q i * a i := by
    calc
      lam * (∑ i ∈ s, a i) ≤ ∑ i ∈ s, volume (V i).shade := by
        simpa only [a] using hlam
      _ = ∑ i ∈ s, q i * a i := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [q, a]
        exact (ENNReal.div_mul_cancel (hVpos i hi) (V i).isCompact.measure_ne_top).symm
  have ha : ∀ i ∈ s, ∀ j ∈ s,
      a i ≤ (Metric.volume_comparison.C 3 : ENNReal) * a j := by
    intro i hi j hj
    simpa only [a, hdim] using
      Metric.thickness.volume_comparison
        (V := fun i ↦ (V i).toConvexSpaceBody) hunif i hi j hj
  have hb : ∀ i ∈ s, ∀ j ∈ s,
      b i ≤ (Metric.volume_comparison.C 2 : ENNReal) * b j := by
    intro i hi j hj
    simpa only [b] using
      ConvexSpaceBody.IsFrostmanIn.volume_le_of_thickness_le_affineSubspace
        (hunif' i hi j hj)
  have hcross : ∀ i ∈ s, ∀ j ∈ s, a i * b j ≤ R * b i * a j := by
    intro i hi j hj
    calc
      a i * b j ≤
          ((Metric.volume_comparison.C 3 : ENNReal) * a j) *
            ((Metric.volume_comparison.C 2 : ENNReal) * b i) :=
        mul_le_mul (ha i hi j hj) (hb j hj i hi) bot_le bot_le
      _ = R * b i * a j := by
        simp only [R, aggregateProjectionWeightConst, ENNReal.coe_mul]
        ring
  have htransfer : lam * (∑ i ∈ s, b i) ≤ R * (∑ i ∈ s, q i * b i) :=
    weightedAverage_transfer_of_cross_comparable s a b q lam R hA0 hAtop hcross havg
  have hR0 : R ≠ 0 := by
    exact ENNReal.coe_ne_zero.mpr (mul_ne_zero
      (Metric.volume_comparison.C_pos 3).ne' (Metric.volume_comparison.C_pos 2).ne')
  have hRtop : R ≠ ⊤ := ENNReal.coe_ne_top
  let cproj : ENNReal := (IsConvexSet.volume_cthickening_ge_of_volume_ge.c 3 : ENNReal) *
    (projectionVolumeComparisonConst : ENNReal)⁻¹ *
      (projectionVolumeComparisonConst : ENNReal)⁻¹
  have hprojected : ∀ i ∈ s,
      cproj * (q i * b i) ≤ volume (Vproj i).shade := by
    intro i hi
    have hqi : q i * volume (V i).carrier ≤ volume (V i).shade := by
      simp only [q]
      exact (ENNReal.div_mul_cancel (hVpos i hi) (V i).isCompact.measure_ne_top).le
    simpa only [cproj, q, b, Vproj, mul_assoc, mul_comm, mul_left_comm] using
      cordoba_hfull (A := A) hdim hcodim (lam := q i) (rn := rn) hrn (V i)
        (hVpos := hVpos i hi) (hlam := hqi)
        (hslabY := hslabY_i i hi) (hslab := hslab_i i hi)
  have hfull' : μ * (∑ i ∈ s, volume (Vproj i).carrier) ≤
      ∑ i ∈ s, volume (Vproj i).shade := by
    calc
      μ * (∑ i ∈ s, volume (Vproj i).carrier) =
          R⁻¹ * cproj * (lam * ∑ i ∈ s, b i) := by
        simp only [μ, R, cproj, b]
        ring
      _ ≤ R⁻¹ * cproj * (R * ∑ i ∈ s, q i * b i) := by gcongr
      _ = cproj * ∑ i ∈ s, q i * b i := by
        rw [show R⁻¹ * cproj * (R * ∑ i ∈ s, q i * b i) =
          (R⁻¹ * R) * (cproj * ∑ i ∈ s, q i * b i) by ring,
          ENNReal.inv_mul_cancel hR0 hRtop, one_mul]
      _ ≤ ∑ i ∈ s, volume (Vproj i).shade := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum hprojected
  -- Frostman property of the projected family with the projected constant.
  have hFro' :
      ConvexSpaceBody.IsFrostmanIn s (fun i => (Vproj i).toConvexSpaceBody) Kproj Cproj := hFroProj
  -- The affine planar Cordoba estimate.
  exact ConvexSpaceBody.IsFrostmanIn.le_volume_biUnion_TwoDim_affineSubspace_aggregate
    (V := Vproj) (K := Kproj) (C := Cproj) (μ := μ) (N := N + 16)
    hne hN' hunif' hsub' hvol' hfull' hFro'

/-- Córdoba projection bound under the ordinary, unthickened Frostman hypothesis. -/
private lemma cordoba_proj_le {A : AffineSubspace ℝ E} [Nonempty ↑A]
    (K : ConvexSpaceBody E) {C lam : ENNReal} {N : ℕ} {rn : NNReal}
    (hdim : Module.finrank ℝ E = 3)
    (hAdim : Module.finrank ℝ A.direction = 2)
    (hcodim : Module.finrank ℝ E = Module.finrank ℝ A.direction + 1)
    (hrn : rn ≠ 0)
    (hrnscale : (rn : ENNReal) ≤ Metric.ethickness.scale ℝ K.carrier)
    (hAsub : K.carrier ⊆ Metric.cthickening (rn : ℝ) (A : Set E))
    (hKt : (thickBody rn K).carrier
      ⊆ Metric.cthickening ((3 * rn : NNReal) : ℝ) (A : Set E))
    (hsub : ∀ i ∈ s, (V i).carrier ⊆ K.carrier)
    (hFr : ConvexSpaceBody.IsFrostmanIn s (fun i => (V i).toConvexSpaceBody) K C)
    (hne : s.Nonempty)
    (hVpos : ∀ i ∈ s, volume (V i).carrier ≠ 0)
    (hlam : lam * (∑ i ∈ s, volume (V i).carrier) ≤
      ∑ i ∈ s, volume (V i).shade)
    (hunif : ∀ i ∈ s, ∀ j ∈ s,
      Metric.thickness ℝ (V i).carrier ≤ 2 • Metric.thickness ℝ (V j).carrier)
    (hN : ∀ i ∈ s, volume K.carrier ≤ 2 ^ N * volume (V i).carrier) :
    (ConvexSpaceBody.IsFrostmanIn.le_volume_biUnion_TwoDim.c : ENNReal) *
        ((aggregateProjectionWeightConst : ENNReal)⁻¹ *
          (IsConvexSet.volume_cthickening_ge_of_volume_ge.c 3 : ENNReal) * lam
          * (projectionVolumeComparisonConst : ENNReal)⁻¹
          * (projectionVolumeComparisonConst : ENNReal)⁻¹) ^ 2 *
        volume ((slabProductBody A (thickBody rn K) (3 * rn) hKt).orthogonalProjectionImage
          A).carrier
      ≤ (((N + 16 : ℕ) : ENNReal) + 1) *
          ((projectionVolumeComparisonConst : ENNReal) *
            ((1 + (thickeningRatioConst 3 : ENNReal) ^ 2) *
              (productBodyVolumeRatioConst : ENNReal) * C)) *
          volume (⋃ i ∈ s,
            ((thickShaded rn (V i)).orthogonalProjectionImage A
              (isClosed_thickShaded_shade rn (V i))).shade) := by
  let P : ConvexSpaceBody E := slabProductBody A (thickBody rn K) (3 * rn) hKt
  have hslab_i : ∀ i ∈ s, (thickBody rn (V i).toConvexSpaceBody).carrier
      ⊆ Metric.cthickening ((3 * rn : NNReal) : ℝ) (A : Set E) := by
    intro i hi
    rw [show (3 * rn : NNReal) = 2 * rn + rn by ring]
    exact cthickening_subset_cthickening_affineSubspace (A := A) (X := (V i).carrier)
      (a := 2 * rn) (b := rn) ((hsub i hi).trans hAsub)
  have hVtP : ∀ i ∈ s, thickBody rn (V i).toConvexSpaceBody ≤ P := by
    intro i hi
    have hthick_sub :
        (thickBody rn (V i).toConvexSpaceBody).carrier ⊆ (thickBody rn K).carrier :=
      Metric.cthickening_subset_of_subset ((2 * rn : NNReal) : ℝ) (hsub i hi)
    rw [SetLike.le_def]
    exact fun x hx =>
      ⟨Set.mem_image_of_mem (orthogonalProjection A) (hthick_sub hx), hslab_i i hi hx⟩
  have hP : volume P.carrier ≤
      (productBodyVolumeRatioConst : ENNReal) * volume K.carrier :=
    slabProductBody_volume_le (A := A) hdim K hrnscale hKt
  have hFroPsmall : ConvexSpaceBody.IsFrostmanIn s
      (fun i => thickBody rn (V i).toConvexSpaceBody) P
      ((thickeningRatioConst 3 : ENNReal) ^ 2 *
        (productBodyVolumeRatioConst : ENNReal) * C) :=
    frostman_thickened s V hdim K P hsub hFr hne hVpos hunif hVtP hP
  have hFroP : ConvexSpaceBody.IsFrostmanIn s
      (fun i => thickBody rn (V i).toConvexSpaceBody) P
      ((1 + (thickeningRatioConst 3 : ENNReal) ^ 2) *
        (productBodyVolumeRatioConst : ENNReal) * C) := by
    intro Q hQP
    refine (hFroPsmall Q hQP).trans ?_
    gcongr
    exact le_add_self
  exact cordoba_proj_le_of_thickenedFrostmanInProduct s V K hdim hAdim hcodim hrn
    hrnscale hAsub hKt hsub hFroP hne hVpos hlam hunif hN

/-- Córdoba projection bound under GWZ Remark 5.3's division-free Frostman hypothesis for the
inner carriers thickened at the shortest outer scale. -/
private lemma cordoba_proj_le_of_thickenedFrostman {A : AffineSubspace ℝ E} [Nonempty ↑A]
    (K : ConvexSpaceBody E) {C lam : ENNReal} {N : ℕ} {rn : NNReal}
    (hdim : Module.finrank ℝ E = 3)
    (hAdim : Module.finrank ℝ A.direction = 2)
    (hcodim : Module.finrank ℝ E = Module.finrank ℝ A.direction + 1)
    (hrn : rn ≠ 0)
    (hrnscale : (rn : ENNReal) ≤ Metric.ethickness.scale ℝ K.carrier)
    (hAsub : K.carrier ⊆ Metric.cthickening (rn : ℝ) (A : Set E))
    (hKt : (thickBody rn K).carrier
      ⊆ Metric.cthickening ((3 * rn : NNReal) : ℝ) (A : Set E))
    (hsub : ∀ i ∈ s, (V i).carrier ⊆ K.carrier)
    (hFr : Kakeya.maxDensity s (fun i => thickBody rn (V i).toConvexSpaceBody) *
      volume K.carrier ≤
        C * ∑ i ∈ s, volume (thickBody rn (V i).toConvexSpaceBody).carrier)
    (hne : s.Nonempty)
    (hVpos : ∀ i ∈ s, volume (V i).carrier ≠ 0)
    (hlam : lam * (∑ i ∈ s, volume (V i).carrier) ≤
      ∑ i ∈ s, volume (V i).shade)
    (hunif : ∀ i ∈ s, ∀ j ∈ s,
      Metric.thickness ℝ (V i).carrier ≤ 2 • Metric.thickness ℝ (V j).carrier)
    (hN : ∀ i ∈ s, volume K.carrier ≤ 2 ^ N * volume (V i).carrier) :
    (ConvexSpaceBody.IsFrostmanIn.le_volume_biUnion_TwoDim.c : ENNReal) *
        ((aggregateProjectionWeightConst : ENNReal)⁻¹ *
          (IsConvexSet.volume_cthickening_ge_of_volume_ge.c 3 : ENNReal) * lam
          * (projectionVolumeComparisonConst : ENNReal)⁻¹
          * (projectionVolumeComparisonConst : ENNReal)⁻¹) ^ 2 *
        volume ((slabProductBody A (thickBody rn K) (3 * rn) hKt).orthogonalProjectionImage
          A).carrier
      ≤ (((N + 16 : ℕ) : ENNReal) + 1) *
          ((projectionVolumeComparisonConst : ENNReal) *
            ((1 + (thickeningRatioConst 3 : ENNReal) ^ 2) *
              (productBodyVolumeRatioConst : ENNReal) * C)) *
          volume (⋃ i ∈ s,
            ((thickShaded rn (V i)).orthogonalProjectionImage A
              (isClosed_thickShaded_shade rn (V i))).shade) := by
  let P : ConvexSpaceBody E := slabProductBody A (thickBody rn K) (3 * rn) hKt
  let Wt : ι → ConvexSpaceBody E := fun i => thickBody rn (V i).toConvexSpaceBody
  have hslab_i : ∀ i ∈ s, (Wt i).carrier
      ⊆ Metric.cthickening ((3 * rn : NNReal) : ℝ) (A : Set E) := by
    intro i hi
    rw [show (3 * rn : NNReal) = 2 * rn + rn by ring]
    exact cthickening_subset_cthickening_affineSubspace (A := A) (X := (V i).carrier)
      (a := 2 * rn) (b := rn) ((hsub i hi).trans hAsub)
  have hVtP : ∀ i ∈ s, Wt i ≤ P := by
    intro i hi
    have hthick_sub : (Wt i).carrier ⊆ (thickBody rn K).carrier :=
      Metric.cthickening_subset_of_subset ((2 * rn : NNReal) : ℝ) (hsub i hi)
    rw [SetLike.le_def]
    exact fun x hx =>
      ⟨Set.mem_image_of_mem (orthogonalProjection A) (hthick_sub hx), hslab_i i hi hx⟩
  have hP : volume P.carrier ≤
      (productBodyVolumeRatioConst : ENNReal) * volume K.carrier :=
    slabProductBody_volume_le (A := A) hdim K hrnscale hKt
  obtain ⟨i₀, hi₀⟩ := hne
  have hViP : (V i₀).toConvexSpaceBody ≤ P := by
    exact (ConvexSpaceBody.self_le_cthickening (V i₀).toConvexSpaceBody
      ((2 * rn : NNReal) : ℝ)).trans (hVtP i₀ hi₀)
  have hP0 : volume P.carrier ≠ 0 := fun hzero =>
    hVpos i₀ hi₀ (measure_mono_null (SetLike.coe_subset_coe.mpr hViP) hzero)
  have hmax : Kakeya.maxDensity s Wt * volume P.carrier ≤
      ((1 + (thickeningRatioConst 3 : ENNReal) ^ 2) *
          (productBodyVolumeRatioConst : ENNReal) * C) *
        ∑ i ∈ s, volume (Wt i).carrier := by
    calc
      Kakeya.maxDensity s Wt * volume P.carrier ≤
          Kakeya.maxDensity s Wt *
            ((productBodyVolumeRatioConst : ENNReal) * volume K.carrier) := by gcongr
      _ = (productBodyVolumeRatioConst : ENNReal) *
          (Kakeya.maxDensity s Wt * volume K.carrier) := by ring
      _ ≤ (productBodyVolumeRatioConst : ENNReal) *
          (C * ∑ i ∈ s, volume (Wt i).carrier) := by
            calc
              (productBodyVolumeRatioConst : ENNReal) *
                    (Kakeya.maxDensity s Wt * volume K.carrier) =
                  (Kakeya.maxDensity s Wt * volume K.carrier) *
                    (productBodyVolumeRatioConst : ENNReal) := mul_comm _ _
              _ ≤ (C * ∑ i ∈ s, volume (Wt i).carrier) *
                    (productBodyVolumeRatioConst : ENNReal) :=
                by
                  simpa only [Wt, mul_comm] using
                    mul_le_mul_right hFr (productBodyVolumeRatioConst : ENNReal)
              _ = (productBodyVolumeRatioConst : ENNReal) *
                  (C * ∑ i ∈ s, volume (Wt i).carrier) := mul_comm _ _
      _ ≤ ((1 + (thickeningRatioConst 3 : ENNReal) ^ 2) *
          (productBodyVolumeRatioConst : ENNReal) * C) *
            ∑ i ∈ s, volume (Wt i).carrier := by
              rw [show
                ((1 + (thickeningRatioConst 3 : ENNReal) ^ 2) *
                    (productBodyVolumeRatioConst : ENNReal) * C) *
                      ∑ i ∈ s, volume (Wt i).carrier =
                  (productBodyVolumeRatioConst : ENNReal) *
                      (C * ∑ i ∈ s, volume (Wt i).carrier) +
                    (thickeningRatioConst 3 : ENNReal) ^ 2 *
                      ((productBodyVolumeRatioConst : ENNReal) *
                        (C * ∑ i ∈ s, volume (Wt i).carrier)) by ring]
              exact le_self_add
  have hFroP : ConvexSpaceBody.IsFrostmanIn s Wt P
      ((1 + (thickeningRatioConst 3 : ENNReal) ^ 2) *
        (productBodyVolumeRatioConst : ENNReal) * C) :=
    ConvexSpaceBody.IsFrostmanIn.of_maxDensity_mul_volume_le hVtP hP0 hmax
  exact cordoba_proj_le_of_thickenedFrostmanInProduct s V K hdim hAdim hcodim hrn
    hrnscale hAsub hKt hsub hFroP ⟨i₀, hi₀⟩ hVpos hlam hunif hN

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- LHS comparison: the shadow of `N_r(K)` is contained in the shadow of the slab product body. -/
private lemma lhs_shadow_mono {A : AffineSubspace ℝ E} [Nonempty ↑A]
    (K : ConvexSpaceBody E) {rn : NNReal}
    (hKt : (thickBody rn K).carrier
      ⊆ Metric.cthickening ((3 * rn : NNReal) : ℝ) (A : Set E)) :
    orthogonalProjection A '' (K.cthickening (rn : ℝ)).carrier
      ⊆ ((slabProductBody A (thickBody rn K) (3 * rn) hKt).orthogonalProjectionImage
        A).carrier := by
  calc
    orthogonalProjection A '' (K.cthickening (rn : ℝ)).carrier
        = orthogonalProjection A '' (Metric.cthickening (rn : ℝ) K.carrier) := by simp
    _ ⊆ orthogonalProjection A '' (Metric.cthickening (2 * (rn : ℝ)) K.carrier) := by
      exact Set.image_mono
        (Metric.cthickening_mono (by linarith [NNReal.coe_nonneg rn]) K.carrier)
    _ = orthogonalProjection A '' (thickBody rn K).carrier := by simp [thickBody]
    _ = orthogonalProjection A '' (slabProductBody A (thickBody rn K) (3 * rn) hKt).carrier := by
      rw [image_slabProductBody]
    _ = ((slabProductBody A (thickBody rn K) (3 * rn) hKt).orthogonalProjectionImage
          A).carrier := by
      exact (ConvexSpaceBody.coe_orthogonalProjectionImage
        (slabProductBody A (thickBody rn K) (3 * rn) hKt) A).symm

omit [Nontrivial E] in
/-- RHS fibre lift for the `r/2`-thickened shadings: the full `r/2`-normal fibres over the
projected union of thickened shadings lie inside `N_r(U) ⊆ N_{2r}(U) ∩ N_r(K)`, the induced
shading. -/
private lemma rhs_proj_le_thickened {A : AffineSubspace ℝ E} [Nonempty ↑A] (K : ConvexSpaceBody E)
    {rn : NNReal}
    (hcodim : Module.finrank ℝ E = Module.finrank ℝ A.direction + 1)
    (hrn : (rn : ℝ) = Metric.thickness ℝ K.carrier (Module.finrank ℝ E - 1))
    (hsub : ∀ i ∈ s, (V i).carrier ⊆ K.carrier)
    (hYclosed : ∀ i ∈ s, IsClosed (V i).shade) :
    (rn : ENNReal) *
        volume (⋃ i ∈ s,
          ((thickShaded rn (V i)).orthogonalProjectionImage A
            (isClosed_thickShaded_shade rn (V i))).shade)
      ≤ volume (inducedShading s V K).shade := by
  set r := Metric.thickness ℝ K.carrier (Module.finrank ℝ E - 1) with hr
  have hr_nonneg : 0 ≤ r := Metric.thickness_nonneg _ _
  set ρ : ℝ := ((rn / 2 : NNReal) : ℝ) with hρ
  have hρ_nonneg : 0 ≤ ρ := by
    rw [hρ]
    exact NNReal.coe_nonneg _
  set U : Set E := ⋃ i ∈ s, (V i).shade with hU
  -- U ⊆ K.carrier: each shade lies in its carrier which lies in K.carrier.
  have hU_sub : U ⊆ K.carrier := by
    rw [hU]
    exact Set.iUnion₂_subset fun i hi ↦ (V i).shade_subset.trans (hsub i hi)
  -- Each shade lies in the union `U`.
  have hVi_sub_U : ∀ i ∈ s, (V i).shade ⊆ U := by
    intro i hi
    rw [hU]
    intro z hz
    exact Set.mem_iUnion₂.mpr ⟨i, hi, hz⟩
  -- The projected `ρ`-thickened union is measurable: each shade is closed, hence compact (closed
  -- subset of the compact carrier), the finite union is compact, its `ρ`-thickening is compact,
  -- and the continuous image of a compact set is compact, hence closed, hence measurable.
  have hπN_meas : MeasurableSet (orthogonalProjection A '' (Metric.cthickening ρ U)) := by
    have h_compact_shades : ∀ i ∈ s, IsCompact ((V i).shade) := fun i hi =>
      (V i).isCompact'.of_isClosed_subset (hYclosed i hi) (V i).shade_subset
    have h_compact_U : IsCompact U := by
      rw [hU]
      exact Finset.isCompact_biUnion s h_compact_shades
    have h_compact_thick : IsCompact (Metric.cthickening ρ U) := h_compact_U.cthickening
    have h_compact_image : IsCompact (orthogonalProjection A '' (Metric.cthickening ρ U)) :=
      h_compact_thick.image (orthogonalProjection A).cont
    exact h_compact_image.isClosed.measurableSet
  -- The projected union of the thickened shadings is contained in the projection of the
  -- `ρ`-thickening of the union `U`.
  have hunion_sub : (⋃ i ∈ s,
        orthogonalProjection A '' (Metric.cthickening ρ ((V i).shade)))
      ⊆ orthogonalProjection A '' (Metric.cthickening ρ U) := by
    intro y hy
    rw [Set.mem_iUnion] at hy
    rcases hy with ⟨i, hyi⟩
    rw [Set.mem_iUnion] at hyi
    rcases hyi with ⟨hi, hyi⟩
    rw [Set.mem_image] at hyi
    rcases hyi with ⟨x, hx, hxy⟩
    rw [← hxy]
    exact Set.mem_image_of_mem (orthogonalProjection A)
      (Metric.cthickening_subset_of_subset ρ (hVi_sub_U i hi) hx)
  -- Fiber lower bound: the full `ρ`-normal fibers over `π(N_ρ(U))` lie in `N_ρ(N_ρ(U))`.
  have hfiber : 2 * ENNReal.ofReal ρ * volume (orthogonalProjection A '' (Metric.cthickening ρ U))
      ≤ volume (Metric.cthickening ρ (Metric.cthickening ρ U)) :=
    two_mul_ofReal_mul_volume_orthogonalProjection_image_le_volume_cthickening A hcodim
      hρ_nonneg hπN_meas
  -- The fibre factor: `(rn : ℝ) = 2 · ρ`, hence `(rn : ENNReal) = 2 · ENNReal.ofReal ρ`.
  have hrnρ : (rn : ℝ) = 2 * ρ := by
    rw [hρ]
    rw [NNReal.coe_div]
    field_simp
    norm_num
  have hrn_factor : (rn : ENNReal) = 2 * ENNReal.ofReal ρ := by
    calc
      (rn : ENNReal) = ENNReal.ofReal (rn : ℝ) := (ENNReal.ofReal_coe_nnreal (p := rn)).symm
      _ = ENNReal.ofReal (2 * ρ) := by rw [hrnρ]
      _ = ENNReal.ofReal (2 : ℝ) * ENNReal.ofReal ρ := by
        rw [ENNReal.ofReal_mul (by norm_num : 0 ≤ (2 : ℝ))]
      _ = (2 : ENNReal) * ENNReal.ofReal ρ := by norm_num
  -- `N_ρ(N_ρ(U)) ⊆ N_{2ρ}(U) = N_r(U)`.
  have hNρNρ : Metric.cthickening ρ (Metric.cthickening ρ U) ⊆ Metric.cthickening r U := by
    have hρρ : ρ + ρ = r := by
      rw [← two_mul]
      exact hrnρ.symm.trans hrn
    calc
      Metric.cthickening ρ (Metric.cthickening ρ U) ⊆ Metric.cthickening (ρ + ρ) U :=
        Metric.cthickening_cthickening_subset hρ_nonneg hρ_nonneg U
      _ = Metric.cthickening r U := by rw [hρρ]
  -- Containment: `N_r(U) ⊆ N_{2r}(U) ∩ N_r(K)` (here `K.scale = r`).
  have hcont : Metric.cthickening r U ⊆ (inducedShading s V K).shade := by
    rw [ShadedBody.shade_inducedShading, hU]
    rw [show K.scale = r from rfl]
    intro x hx
    exact ⟨Metric.cthickening_mono (by nlinarith [hr_nonneg]) _ hx,
      Metric.cthickening_subset_of_subset r hU_sub hx⟩
  -- Assemble.
  calc
    (rn : ENNReal) *
        volume (⋃ i ∈ s,
          ((thickShaded rn (V i)).orthogonalProjectionImage A
            (isClosed_thickShaded_shade rn (V i))).shade)
        = (rn : ENNReal) *
            volume (⋃ i ∈ s, orthogonalProjection A '' (Metric.cthickening ρ ((V i).shade))) := by
          simp [thickShaded, orthogonalProjectionImage, hρ]
    _ ≤ (rn : ENNReal) * volume (orthogonalProjection A '' (Metric.cthickening ρ U)) := by
          exact mul_le_mul_right (measure_mono hunion_sub) (rn : ENNReal)
    _ = 2 * ENNReal.ofReal ρ * volume (orthogonalProjection A '' (Metric.cthickening ρ U)) := by
          rw [hrn_factor]
    _ ≤ volume (Metric.cthickening ρ (Metric.cthickening ρ U)) := hfiber
    _ ≤ volume (Metric.cthickening r U) := measure_mono hNρNρ
    _ ≤ volume (inducedShading s V K).shade := measure_mono hcont

omit [MeasurableSpace E] [BorelSpace E] in
/-- The `ethickness` scale of a convex body is the `ENNReal` form of its shortest affine
thickness. -/
private lemma scale_eq_ofReal_thickness (K : ConvexSpaceBody E) :
    Metric.ethickness.scale ℝ K.carrier
      = ENNReal.ofReal (Metric.thickness ℝ K.carrier (Module.finrank ℝ E - 1)) := by
  rw [Metric.ethickness.scale_eq]
  exact Metric.ethickness_thickness' (K.isCompact.isBounded) (Module.finrank ℝ E - 1)

omit [Nontrivial E] in
/-- A convex body of positive volume has positive shortest affine thickness: otherwise it would be
contained in a proper affine subspace, which is null. -/
private lemma thickness_pos_of_volume_ne_zero {A : AffineSubspace ℝ E}
    (K : ConvexSpaceBody E) (hAdim : Module.finrank ℝ A.direction < Module.finrank ℝ E)
    (hAsub : K.carrier ⊆
      Metric.cthickening (Metric.thickness ℝ K.carrier (Module.finrank ℝ E - 1)) A)
    (hK : volume K.carrier ≠ 0) :
    0 < Metric.thickness ℝ K.carrier (Module.finrank ℝ E - 1) := by
  by_contra hnot
  have hthick0 : Metric.thickness ℝ K.carrier (Module.finrank ℝ E - 1) = 0 := by
    exact le_antisymm (le_of_not_gt hnot) (Metric.thickness_nonneg _ _)
  have hsub0 : K.carrier ⊆ Metric.cthickening 0 (A : Set E) := by
    simpa [hthick0] using hAsub
  have hsubA : K.carrier ⊆ (A : Set E) := by
    calc
      K.carrier ⊆ Metric.cthickening 0 (A : Set E) := hsub0
      _ = closure (A : Set E) := Metric.cthickening_zero (A : Set E)
      _ = (A : Set E) := A.closed_of_finiteDimensional.closure_eq
  have hAproper : A ≠ ⊤ := by
    intro hAtop
    have hle : Module.finrank ℝ E ≤ Module.finrank ℝ A.direction := by
      rw [hAtop, AffineSubspace.direction_top, finrank_top]
    exact (not_lt_of_ge hle) hAdim
  have hvolA : volume (A : Set E) = 0 :=
    MeasureTheory.Measure.addHaar_affineSubspace volume A hAproper
  exact hK (measure_mono_null hsubA hvolA)

set_option maxHeartbeats 800000 in
-- Elaborating the shared ordinary/Remark 5.3 Córdoba branch requires a larger reduction budget.
/-- Aggregate single-body form of GWZ Lemma 5.9.
Setup as in `lambdaInducedSingleW`: `r` is the shortest affine thickness of `K`, and the induced
shaded body has carrier `N_r(K)` and shade `N_{2r}(U(𝒱, Y)) ∩ N_r(K)`.

Only the aggregate density bound `lam · ∑ |V i| ≤ ∑ |Y i|` is assumed.  The proof transfers this
average to the projected carrier weights and applies the aggregate planar Córdoba estimate. -/
private lemma lambdaInducedSingleWAggregate_aux {C lam : ENNReal} {N : ℕ}
    (hdim : Module.finrank ℝ E = 3)
    (K : ConvexSpaceBody E)
    (hsub : ∀ i ∈ s, (V i).carrier ⊆ K.carrier)
    (hFr : ConvexSpaceBody.IsFrostmanIn s (fun i => (V i).toConvexSpaceBody) K C ∨
      Kakeya.maxDensity s (fun i =>
          (V i).toConvexSpaceBody.cthickening (2 * K.scale)) * volume K.carrier ≤
        C * ∑ i ∈ s,
          volume ((V i).toConvexSpaceBody.cthickening (2 * K.scale)).carrier)
    (hne : s.Nonempty)
    (hVpos : ∀ i ∈ s, volume (V i).carrier ≠ 0)
    (hlam : lam * (∑ i ∈ s, volume (V i).carrier) ≤
      ∑ i ∈ s, volume (V i).shade)
    (hunif : ∀ i ∈ s, ∀ j ∈ s,
      Metric.thickness ℝ (V i).carrier ≤ 2 • Metric.thickness ℝ (V j).carrier)
    (hN : ∀ i ∈ s, volume K.carrier ≤ 2 ^ N * volume (V i).carrier)
    (hYclosed : ∀ i ∈ s, IsClosed (V i).shade) :
    C⁻¹ * lam ^ 2 *
        volume (K.cthickening
          (Metric.thickness ℝ K.carrier (Module.finrank ℝ E - 1))).carrier
      ≤ (lambdaInducedSingleWUniform.C : ENNReal) * ((N : ENNReal) + 1) *
        volume (inducedShading (s := s) (V := V) K).shade := by
  obtain ⟨A, hAne, hAdim, hAsub0⟩ := exists_twoDim_slab K hdim
  haveI : Nonempty (↑A : Set E) := hAne.to_subtype
  rw [coe_lambdaInducedSingleWUniform_C]
  have h2 : Module.finrank ℝ E - 1 = 2 := by rw [hdim]
  have hcodim : Module.finrank ℝ E = Module.finrank ℝ A.direction + 1 := by rw [hdim, hAdim]
  have hAsub : K.carrier ⊆ Metric.cthickening
      (Metric.thickness ℝ K.carrier (Module.finrank ℝ E - 1)) A := by
    simpa [h2] using hAsub0
  -- `|K| > 0`, hence the shortest affine thickness `r` of `K` is positive.
  obtain ⟨i₀, hi₀⟩ := hne
  have hKpos : volume K.carrier ≠ 0 := fun h =>
    hVpos i₀ hi₀ (measure_mono_null (hsub i₀ hi₀) h)
  have hrpos : 0 < Metric.thickness ℝ K.carrier (Module.finrank ℝ E - 1) :=
    thickness_pos_of_volume_ne_zero (A := A) K (by rw [hdim, hAdim]; norm_num) hAsub hKpos
  set r : ℝ := Metric.thickness ℝ K.carrier (Module.finrank ℝ E - 1) with hrdef
  set rn : NNReal := r.toNNReal with hrndef
  have hrn : (rn : ℝ) = r := Real.coe_toNNReal r hrpos.le
  have hrn0 : rn ≠ 0 := by
    simp only [hrndef, ne_eq, Real.toNNReal_eq_zero, not_le]
    exact hrpos
  have hrnscale : (rn : ENNReal) ≤ Metric.ethickness.scale ℝ K.carrier := by
    rw [scale_eq_ofReal_thickness, ← hrdef, ← hrn, ENNReal.ofReal_coe_nnreal]
  have hAsub' : K.carrier ⊆ Metric.cthickening (rn : ℝ) (A : Set E) := by rw [hrn]; exact hAsub
  have htworn : ((2 * rn : NNReal) : ℝ) = 2 * K.scale := by
    rw [NNReal.coe_mul, hrn, hrdef]
    norm_num
  have hKt : (thickBody rn K).carrier
      ⊆ Metric.cthickening ((3 * rn : NNReal) : ℝ) (A : Set E) := by
    have := cthickening_subset_cthickening_affineSubspace (A := A) (a := 2 * rn) (b := rn) hAsub'
    simpa [thickBody, show (2 : NNReal) * rn + rn = 3 * rn by ring] using this
  have hc₂0 : (ConvexSpaceBody.IsFrostmanIn.le_volume_biUnion_TwoDim.c : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr (ConvexSpaceBody.IsFrostmanIn.le_volume_biUnion_TwoDim.c_pos).ne'
  have hcth0 : (IsConvexSet.volume_cthickening_ge_of_volume_ge.c 3 : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr (IsConvexSet.volume_cthickening_ge_of_volume_ge.c_pos 3).ne'
  have hD0 : (projectionVolumeComparisonConst : ENNReal) ≠ 0 := by
    refine ENNReal.coe_ne_zero.mpr ?_
    simp [projectionVolumeComparisonConst, cthickeningDoublingConst,
      Metric.lt_volume_convexHull.c, Nat.factorial]
  let R : ENNReal := aggregateProjectionWeightConst
  have hR0 : R ≠ 0 := ENNReal.coe_ne_zero.mpr (mul_ne_zero
    (Metric.volume_comparison.C_pos 3).ne' (Metric.volume_comparison.C_pos 2).ne')
  have hRtop : R ≠ ⊤ := ENNReal.coe_ne_top
  have hLHS : volume (K.cthickening r).carrier ≤ 2 * (2 * (rn : ENNReal)) *
      volume ((slabProductBody A (thickBody rn K) (3 * rn) hKt).orthogonalProjectionImage
        A).carrier := by
    calc volume (K.cthickening r).carrier
      ≤ 2 * (2 * ENNReal.ofReal r) *
          volume (orthogonalProjection A '' (K.cthickening r).carrier) :=
        lhs_proj_le (A := A) K hcodim hAsub
    _ ≤ 2 * (2 * (rn : ENNReal)) *
          volume ((slabProductBody A (thickBody rn K) (3 * rn) hKt).orthogonalProjectionImage
            A).carrier := by
        rw [← hrn, ENNReal.ofReal_coe_nnreal]
        gcongr
        exact lhs_shadow_mono (A := A) K hKt
  have hcord := hFr.elim
    (fun hFr ↦ cordoba_proj_le s V (A := A) K hdim hAdim hcodim hrn0 hrnscale hAsub'
      hKt hsub hFr ⟨i₀, hi₀⟩ hVpos hlam hunif hN)
    (fun hFr ↦ cordoba_proj_le_of_thickenedFrostman s V (A := A) K hdim hAdim hcodim
      hrn0 hrnscale hAsub' hKt hsub (by
        simpa only [thickBody, htworn] using hFr) ⟨i₀, hi₀⟩ hVpos hlam hunif hN)
  have hcord' :
      (ConvexSpaceBody.IsFrostmanIn.le_volume_biUnion_TwoDim.c : ENNReal) *
          ((IsConvexSet.volume_cthickening_ge_of_volume_ge.c 3 : ENNReal) *
            (R⁻¹ * lam) * (projectionVolumeComparisonConst : ENNReal)⁻¹ *
              (projectionVolumeComparisonConst : ENNReal)⁻¹) ^ 2 *
          volume ((slabProductBody A (thickBody rn K) (3 * rn) hKt).orthogonalProjectionImage
            A).carrier ≤
        (((N + 16 : ℕ) : ENNReal) + 1) *
          ((projectionVolumeComparisonConst : ENNReal) *
            ((1 + (thickeningRatioConst 3 : ENNReal) ^ 2) *
              (productBodyVolumeRatioConst : ENNReal) * C)) *
          volume (⋃ i ∈ s,
            ((thickShaded rn (V i)).orthogonalProjectionImage A
              (isClosed_thickShaded_shade rn (V i))).shade) := by
    simpa only [R, mul_assoc, mul_comm, mul_left_comm] using hcord
  let Cbase : ENNReal :=
    68 * (ConvexSpaceBody.IsFrostmanIn.le_volume_biUnion_TwoDim.c : ENNReal)⁻¹ *
      (IsConvexSet.volume_cthickening_ge_of_volume_ge.c 3 : ENNReal)⁻¹ ^ 2 *
      (projectionVolumeComparisonConst : ENNReal) ^ 5 *
      (1 + (thickeningRatioConst 3 : ENNReal) ^ 2) *
      (productBodyVolumeRatioConst : ENNReal)
  have hbase : C⁻¹ * (R⁻¹ * lam) ^ 2 *
        volume (K.cthickening
          (Metric.thickness ℝ K.carrier (Module.finrank ℝ E - 1))).carrier ≤
      Cbase * ((N : ENNReal) + 1) * volume (inducedShading (s := s) (V := V) K).shade := by
    simpa only [Cbase, hrdef] using
      assemble_bound (r := (rn : ENNReal)) hc₂0 ENNReal.coe_ne_top hcth0
        ENNReal.coe_ne_top hD0 ENNReal.coe_ne_top hLHS hcord'
        (rhs_proj_le_thickened s V (A := A) K hcodim (by rw [hrn]) hsub hYclosed)
  change C⁻¹ * lam ^ 2 *
      volume (K.cthickening
        (Metric.thickness ℝ K.carrier (Module.finrank ℝ E - 1))).carrier ≤
    Cbase * R ^ 2 * ((N : ENNReal) + 1) *
      volume (inducedShading (s := s) (V := V) K).shade
  calc
    C⁻¹ * lam ^ 2 *
          volume (K.cthickening
            (Metric.thickness ℝ K.carrier (Module.finrank ℝ E - 1))).carrier =
        R ^ 2 * (C⁻¹ * (R⁻¹ * lam) ^ 2 *
          volume (K.cthickening
            (Metric.thickness ℝ K.carrier (Module.finrank ℝ E - 1))).carrier) := by
      rw [show R ^ 2 * (C⁻¹ * (R⁻¹ * lam) ^ 2 *
          volume (K.cthickening
            (Metric.thickness ℝ K.carrier (Module.finrank ℝ E - 1))).carrier) =
        (R * R⁻¹) ^ 2 * (C⁻¹ * lam ^ 2 *
          volume (K.cthickening
            (Metric.thickness ℝ K.carrier (Module.finrank ℝ E - 1))).carrier) by ring,
        ENNReal.mul_inv_cancel hR0 hRtop]
      simp
    _ ≤ R ^ 2 * (Cbase * ((N : ENNReal) + 1) *
        volume (inducedShading (s := s) (V := V) K).shade) := by gcongr
    _ = Cbase * R ^ 2 * ((N : ENNReal) + 1) *
        volume (inducedShading (s := s) (V := V) K).shade := by ring

set_option maxHeartbeats 800000 in
-- This wrapper elaborates the large shared aggregate Córdoba conclusion.
/-- Aggregate single-body form of GWZ Lemma 5.9 under the ordinary fibrewise Frostman
hypothesis. -/
lemma lambdaInducedSingleWAggregate {C lam : ENNReal} {N : ℕ}
    (hdim : Module.finrank ℝ E = 3)
    (K : ConvexSpaceBody E)
    (hsub : ∀ i ∈ s, (V i).carrier ⊆ K.carrier)
    (hFr : ConvexSpaceBody.IsFrostmanIn s (fun i => (V i).toConvexSpaceBody) K C)
    (hne : s.Nonempty)
    (hVpos : ∀ i ∈ s, volume (V i).carrier ≠ 0)
    (hlam : lam * (∑ i ∈ s, volume (V i).carrier) ≤
      ∑ i ∈ s, volume (V i).shade)
    (hunif : ∀ i ∈ s, ∀ j ∈ s,
      Metric.thickness ℝ (V i).carrier ≤ 2 • Metric.thickness ℝ (V j).carrier)
    (hN : ∀ i ∈ s, volume K.carrier ≤ 2 ^ N * volume (V i).carrier)
    (hYclosed : ∀ i ∈ s, IsClosed (V i).shade) :
    C⁻¹ * lam ^ 2 *
        volume (K.cthickening
          (Metric.thickness ℝ K.carrier (Module.finrank ℝ E - 1))).carrier
      ≤ (lambdaInducedSingleWUniform.C : ENNReal) * ((N : ENNReal) + 1) *
        volume (inducedShading (s := s) (V := V) K).shade :=
  lambdaInducedSingleWAggregate_aux s V hdim K hsub (Or.inl hFr) hne hVpos hlam hunif hN
    hYclosed

set_option maxHeartbeats 800000 in
-- This wrapper elaborates the large shared aggregate Córdoba conclusion.
/-- Aggregate single-body form of GWZ Lemma 5.9 under GWZ Remark 5.3's Frostman hypothesis
for the inner carriers thickened at the shortest scale of the outer body. -/
lemma lambdaInducedSingleWAggregate_of_thickenedFrostman {C lam : ENNReal} {N : ℕ}
    (hdim : Module.finrank ℝ E = 3)
    (K : ConvexSpaceBody E)
    (hsub : ∀ i ∈ s, (V i).carrier ⊆ K.carrier)
    (hFr : Kakeya.maxDensity s (fun i =>
        (V i).toConvexSpaceBody.cthickening (2 * K.scale)) * volume K.carrier ≤
      C * ∑ i ∈ s,
        volume ((V i).toConvexSpaceBody.cthickening (2 * K.scale)).carrier)
    (hne : s.Nonempty)
    (hVpos : ∀ i ∈ s, volume (V i).carrier ≠ 0)
    (hlam : lam * (∑ i ∈ s, volume (V i).carrier) ≤
      ∑ i ∈ s, volume (V i).shade)
    (hunif : ∀ i ∈ s, ∀ j ∈ s,
      Metric.thickness ℝ (V i).carrier ≤ 2 • Metric.thickness ℝ (V j).carrier)
    (hN : ∀ i ∈ s, volume K.carrier ≤ 2 ^ N * volume (V i).carrier)
    (hYclosed : ∀ i ∈ s, IsClosed (V i).shade) :
    C⁻¹ * lam ^ 2 *
        volume (K.cthickening
          (Metric.thickness ℝ K.carrier (Module.finrank ℝ E - 1))).carrier
      ≤ (lambdaInducedSingleWUniform.C : ENNReal) * ((N : ENNReal) + 1) *
        volume (inducedShading (s := s) (V := V) K).shade :=
  lambdaInducedSingleWAggregate_aux s V hdim K hsub (Or.inr hFr) hne hVpos hlam hunif hN
    hYclosed

/-- Uniform bodywise interface for the aggregate single-body Lemma 5.9. -/
lemma lambdaInducedSingleWUniform {C lam : ENNReal} {N : ℕ}
    (hdim : Module.finrank ℝ E = 3) (K : ConvexSpaceBody E)
    (hsub : ∀ i ∈ s, (V i).carrier ⊆ K.carrier)
    (hFr : ConvexSpaceBody.IsFrostmanIn s (fun i => (V i).toConvexSpaceBody) K C)
    (hne : s.Nonempty)
    (hVpos : ∀ i ∈ s, volume (V i).carrier ≠ 0)
    (hlam : ∀ i ∈ s, lam * volume (V i).carrier ≤ volume (V i).shade)
    (hunif : ∀ i ∈ s, ∀ j ∈ s,
      Metric.thickness ℝ (V i).carrier ≤ 2 • Metric.thickness ℝ (V j).carrier)
    (hN : ∀ i ∈ s, volume K.carrier ≤ 2 ^ N * volume (V i).carrier)
    (hYclosed : ∀ i ∈ s, IsClosed (V i).shade) :
    C⁻¹ * lam ^ 2 *
        volume (K.cthickening
          (Metric.thickness ℝ K.carrier (Module.finrank ℝ E - 1))).carrier
      ≤ (lambdaInducedSingleWUniform.C : ENNReal) * ((N : ENNReal) + 1) *
        volume (inducedShading (s := s) (V := V) K).shade := by
  apply lambdaInducedSingleWAggregate s V hdim K hsub hFr hne hVpos
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum hlam
  · exact hunif
  · exact hN
  · exact hYclosed

/-- Single-body form of GWZ Lemma 5.9. If `r` is the shortest affine thickness of `K`, the
induced shaded body has carrier `N_r(K)` and shade `N_{2r}(U(𝒱, Y)) ∩ N_r(K)`.

Suppose that `𝒱` is `C`-Frostman in `K`, its bodies have pairwise `2`-comparable thicknesses and
eccentricity at most `2 ^ N`, and every surviving body has shading proportion at least `lam / 2`.
The last condition is exactly the output of `discardLowShading` at level `2⁻¹` when `lam` is the
fullness of the family before discarding. Then the induced shade occupies at least a
`C⁻¹ · lam²` proportion of the enlarged carrier, up to the scale-dependent constant
`lambdaForInducedShading.C N`. -/
lemma lambdaInducedSingleW {C lam : ENNReal} {N : ℕ} (hdim : Module.finrank ℝ E = 3)
    (K : ConvexSpaceBody E)
    (hsub : ∀ i ∈ s, (V i).carrier ⊆ K.carrier)
    (hFr : ConvexSpaceBody.IsFrostmanIn s (fun i => (V i).toConvexSpaceBody) K C)
    (hne : s.Nonempty)
    (hVpos : ∀ i ∈ s, volume (V i).carrier ≠ 0)
    (hlam : ∀ i ∈ s,
      (2⁻¹ : ENNReal) * lam * volume (V i).carrier ≤ volume (V i).shade)
    (hunif : ∀ i ∈ s, ∀ j ∈ s,
      Metric.thickness ℝ (V i).carrier ≤ 2 • Metric.thickness ℝ (V j).carrier)
    (hN : ∀ i ∈ s, volume K.carrier ≤ 2 ^ N * volume (V i).carrier)
    (hYclosed : ∀ i ∈ s, IsClosed (V i).shade) :
    C⁻¹ * lam ^ 2 *
        volume (K.cthickening
          (Metric.thickness ℝ K.carrier (Module.finrank ℝ E - 1))).carrier
      ≤ (lambdaForInducedShading.C N : ENNReal) *
        volume (inducedShading (s := s) (V := V) K).shade := by
  have h := lambdaInducedSingleWUniform s V hdim K hsub hFr hne hVpos hlam hunif hN hYclosed
  have hhalf : (4 : ENNReal) * (2⁻¹ : ENNReal) ^ 2 = 1 := by
    calc
      (4 : ENNReal) * (2⁻¹ : ENNReal) ^ 2 =
          (2 * 2⁻¹ : ENNReal) * (2 * 2⁻¹ : ENNReal) := by ring
      _ = 1 := by
        rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
        simp
  rw [coe_lambdaForInducedShading_C]
  calc
    C⁻¹ * lam ^ 2 *
        volume (K.cthickening
          (Metric.thickness ℝ K.carrier (Module.finrank ℝ E - 1))).carrier =
        4 * (C⁻¹ * ((2⁻¹ : ENNReal) * lam) ^ 2 *
          volume (K.cthickening
            (Metric.thickness ℝ K.carrier (Module.finrank ℝ E - 1))).carrier) := by
      calc
        _ = (4 * (2⁻¹ : ENNReal) ^ 2) *
            (C⁻¹ * lam ^ 2 *
              volume (K.cthickening
                (Metric.thickness ℝ K.carrier (Module.finrank ℝ E - 1))).carrier) := by
              rw [hhalf]
              simp
        _ = _ := by ring
    _ ≤ 4 * ((lambdaInducedSingleWUniform.C : ENNReal) * ((N : ENNReal) + 1) *
        volume (inducedShading (s := s) (V := V) K).shade) := by gcongr
    _ = 4 * (lambdaInducedSingleWUniform.C : ENNReal) * ((N : ENNReal) + 1) *
        volume (inducedShading (s := s) (V := V) K).shade := by ring

open Classical in
/-- GWZ Lemma 5.9 (blueprint `lambdaForInducedShading`), the key density lower bound for the
induced shading. This estimate is special to `ℝ³` (hypothesis `hdim`).

The factor family `F` packages the inner and outer bodies, their finite index sets, the parent map,
and the containment of every inner body in its parent. The remaining hypotheses say that every
fiber is nonempty, `C`-Frostman and of eccentricity at most `2 ^ N`, while the whole inner family
has pairwise `2`-comparable thicknesses. Each surviving shade has proportion at least `lam / 2`.
The conclusion applies the single-body estimate in every fiber, with the logarithmic scale loss
recorded by `lambdaForInducedShading.C N`. -/
lemma lambdaForInducedShading {C lam : ENNReal} {N : ℕ}
    (F : FactorFamily E ι κ) (hdim : Module.finrank ℝ E = 3)
    (hshape : F.InnerHasSimilarShape 2)
    (hFrostman : F.HasFrostmanFibers C)
    (hne : ∀ j ∈ F.outerSet, (F.fiber j).Nonempty)
    (hVpos : ∀ i ∈ F.innerSet, volume (F.innerBody i).carrier ≠ 0)
    (hlam : ∀ i ∈ F.innerSet,
      (2⁻¹ : ENNReal) * lam * volume (F.innerBody i).carrier ≤
        volume (F.innerBody i).shade)
    (hN : ∀ j ∈ F.outerSet, ∀ i ∈ F.fiber j,
      volume (F.outerBody j).carrier ≤ 2 ^ N * volume (F.innerBody i).carrier)
    (hYclosed : ∀ i ∈ F.innerSet, IsClosed (F.innerBody i).shade) :
    ∀ j ∈ F.outerSet,
      C⁻¹ * lam ^ 2 *
          volume ((F.outerBody j).cthickening
            (Metric.thickness ℝ (F.outerBody j).carrier
              (Module.finrank ℝ E - 1))).carrier
        ≤ (lambdaForInducedShading.C N : ENNReal) *
          volume (inducedShading (s := F.fiber j) (V := F.innerBody)
            (F.outerBody j)).shade := by
  intro j hj
  apply lambdaInducedSingleW (s := F.fiber j) (V := F.innerBody) hdim (F.outerBody j)
  · intro i hi
    rw [FactorFamily.fiber, Finset.mem_filter] at hi
    change (F.innerBody i).toConvexSpaceBody ≤ F.outerBody j
    simpa [hi.2] using F.inner_le_parent i hi.1
  · exact hFrostman j hj
  · exact hne j hj
  · intro i hi
    exact hVpos i (Finset.mem_filter.mp hi).1
  · intro i hi
    exact hlam i (Finset.mem_filter.mp hi).1
  · intro i hi i' hi' k
    simpa [Pi.smul_apply, nsmul_eq_mul] using
      (hshape i (Finset.mem_filter.mp hi).1 i' (Finset.mem_filter.mp hi').1 k)
  · exact hN j hj
  · intro i hi
    exact hYclosed i (Finset.mem_filter.mp hi).1

open Classical in
/-- **GWZ Lemma 5.9 without a closedness hypothesis** (blueprint
`lem:lambdaForInducedShadingOfMeasurable`): verbatim the statement of `lambdaForInducedShading`
with its hypothesis `hYclosed` deleted and nothing else changed.

The hypothesis is removed rather than propagated: the conclusion mentions the inner shading only
through the induced shading, which by `shade_inducedShading_closureShade` does not distinguish a
shading from its closure, so it suffices to apply `lambdaForInducedShading` to the closure family
`F.closureShade`, whose shades are closed and whose shading masses are no smaller. -/
lemma lambdaForInducedShading_of_measurable {C lam : ENNReal} {N : ℕ}
    (F : FactorFamily E ι κ) (hdim : Module.finrank ℝ E = 3)
    (hshape : F.InnerHasSimilarShape 2)
    (hFrostman : F.HasFrostmanFibers C)
    (hne : ∀ j ∈ F.outerSet, (F.fiber j).Nonempty)
    (hVpos : ∀ i ∈ F.innerSet, volume (F.innerBody i).carrier ≠ 0)
    (hlam : ∀ i ∈ F.innerSet,
      (2⁻¹ : ENNReal) * lam * volume (F.innerBody i).carrier ≤
        volume (F.innerBody i).shade)
    (hN : ∀ j ∈ F.outerSet, ∀ i ∈ F.fiber j,
      volume (F.outerBody j).carrier ≤ 2 ^ N * volume (F.innerBody i).carrier) :
    ∀ j ∈ F.outerSet,
      C⁻¹ * lam ^ 2 *
          volume ((F.outerBody j).cthickening
            (Metric.thickness ℝ (F.outerBody j).carrier
              (Module.finrank ℝ E - 1))).carrier
        ≤ (lambdaForInducedShading.C N : ENNReal) *
          volume (inducedShading (s := F.fiber j) (V := F.innerBody)
            (F.outerBody j)).shade := by
  have hclosed := lambdaForInducedShading F.closureShade hdim
    (hshape := by
      intro i hi i' hi'
      simpa only [FactorFamily.closureShade_innerSet,
        FactorFamily.closureShade_innerBody_carrier] using hshape i hi i' hi')
    (hFrostman := by
      intro j hj
      change ConvexSpaceBody.IsFrostmanIn (F.fiber j)
        (fun i ↦ (F.innerBody i).toConvexSpaceBody) (F.outerBody j) C
      exact hFrostman j (by
        simpa only [FactorFamily.closureShade_outerSet] using hj))
    (hne := by
      intro j hj
      simpa only [FactorFamily.closureShade_outerSet, FactorFamily.closureShade_fiber] using
        hne j hj)
    (hVpos := by
      intro i hi
      simpa only [FactorFamily.closureShade_innerSet,
        FactorFamily.closureShade_innerBody_carrier] using hVpos i hi)
    (hlam := F.closureShade_lambda_le hlam)
    (hN := by
      intro j hj i hi
      simpa only [FactorFamily.closureShade_outerSet, FactorFamily.closureShade_fiber,
        FactorFamily.closureShade_outerBody, FactorFamily.closureShade_innerBody_carrier]
        using hN j hj i hi)
    (hYclosed := by
      intro i _
      exact F.closureShade_isClosed_shade i)
  intro j hj
  have hj' : j ∈ F.closureShade.outerSet := by
    simpa only [FactorFamily.closureShade_outerSet] using hj
  have h := hclosed j hj'
  rw [show F.closureShade.innerBody =
    (fun i ↦ (F.innerBody i).closureShade.toShadedBody) by rfl,
    shade_inducedShading_closureShade] at h
  simpa only [FactorFamily.closureShade_outerBody, FactorFamily.closureShade_fiber] using h

open Classical in
/-- Aggregate measurable form of GWZ Lemma 5.9.

The density parameter may vary by outer block.  For each fiber it is assumed only that the total
shading mass is at least `lam j` times the total carrier mass.  The proof closes every shade,
applies `lambdaInducedSingleWAggregate`, and uses that induced shading is unchanged by closure. -/
private lemma aggregateFullnessForInducedShading_of_measurable_aux {C : ENNReal} {N : ℕ}
    (F : FactorFamily E ι κ) (hdim : Module.finrank ℝ E = 3)
    (hshape : F.InnerHasSimilarShape 2)
    (hFrostman : F.HasFrostmanFibers C ∨ F.HasThickenedFrostmanFibers C)
    (hne : ∀ j ∈ F.outerSet, (F.fiber j).Nonempty)
    (hVpos : ∀ i ∈ F.innerSet, volume (F.innerBody i).carrier ≠ 0)
    (lam : κ → ENNReal)
    (hlam : ∀ j ∈ F.outerSet,
      lam j * (∑ i ∈ F.fiber j, volume (F.innerBody i).carrier) ≤
        ∑ i ∈ F.fiber j, volume (F.innerBody i).shade)
    (hN : ∀ j ∈ F.outerSet, ∀ i ∈ F.fiber j,
      volume (F.outerBody j).carrier ≤ 2 ^ N * volume (F.innerBody i).carrier) :
    ∀ j ∈ F.outerSet,
      C⁻¹ * (lam j) ^ 2 *
          volume ((F.outerBody j).cthickening
            (Metric.thickness ℝ (F.outerBody j).carrier
              (Module.finrank ℝ E - 1))).carrier
        ≤ (lambdaInducedSingleWUniform.C : ENNReal) * ((N : ENNReal) + 1) *
          volume (inducedShading (s := F.fiber j) (V := F.innerBody)
            (F.outerBody j)).shade := by
  intro j hj
  have hjc : j ∈ F.closureShade.outerSet := by
    simpa only [FactorFamily.closureShade_outerSet] using hj
  have hagg : lam j *
        (∑ i ∈ F.closureShade.fiber j, volume (F.closureShade.innerBody i).carrier) ≤
      ∑ i ∈ F.closureShade.fiber j, volume (F.closureShade.innerBody i).shade := by
    calc
      lam j * (∑ i ∈ F.closureShade.fiber j,
          volume (F.closureShade.innerBody i).carrier) =
          lam j * (∑ i ∈ F.fiber j, volume (F.innerBody i).carrier) := by
        simp only [FactorFamily.closureShade_fiber,
          FactorFamily.closureShade_innerBody_carrier]
      _ ≤ ∑ i ∈ F.fiber j, volume (F.innerBody i).shade := hlam j hj
      _ ≤ ∑ i ∈ F.closureShade.fiber j,
          volume (F.closureShade.innerBody i).shade := by
        simp only [FactorFamily.closureShade_fiber]
        exact Finset.sum_le_sum fun i _ ↦
          volume_shade_le_volume_shade_closureShade (F.innerBody i)
  have hsubClosed : ∀ i ∈ F.closureShade.fiber j,
      (F.closureShade.innerBody i).carrier ⊆ (F.closureShade.outerBody j).carrier := by
    intro i hi
    rw [FactorFamily.closureShade_fiber, FactorFamily.fiber, Finset.mem_filter] at hi
    change (F.innerBody i).toConvexSpaceBody ≤ F.outerBody j
    simpa [hi.2] using F.inner_le_parent i hi.1
  have hneClosed : (F.closureShade.fiber j).Nonempty := by
    simpa only [FactorFamily.closureShade_fiber] using hne j hj
  have hVposClosed : ∀ i ∈ F.closureShade.fiber j,
      volume (F.closureShade.innerBody i).carrier ≠ 0 := by
    intro i hi
    rw [FactorFamily.closureShade_fiber] at hi
    simpa only [FactorFamily.closureShade_innerBody_carrier] using
      hVpos i (Finset.mem_filter.mp hi).1
  have hunifClosed : ∀ i ∈ F.closureShade.fiber j, ∀ i' ∈ F.closureShade.fiber j,
      Metric.thickness ℝ (F.closureShade.innerBody i).carrier ≤
        2 • Metric.thickness ℝ (F.closureShade.innerBody i').carrier := by
    intro i hi i' hi' k
    rw [FactorFamily.closureShade_fiber] at hi hi'
    simpa [FactorFamily.closureShade_innerBody_carrier, Pi.smul_apply, nsmul_eq_mul] using
      hshape i (Finset.mem_filter.mp hi).1 i' (Finset.mem_filter.mp hi').1 k
  have hNClosed : ∀ i ∈ F.closureShade.fiber j,
      volume (F.closureShade.outerBody j).carrier ≤
        2 ^ N * volume (F.closureShade.innerBody i).carrier := by
    intro i hi
    rw [FactorFamily.closureShade_fiber] at hi
    simpa only [FactorFamily.closureShade_outerBody,
      FactorFamily.closureShade_innerBody_carrier] using hN j hj i hi
  have hclosed := hFrostman.elim
    (fun hFrostman ↦ lambdaInducedSingleWAggregate
      (s := F.closureShade.fiber j) (V := F.closureShade.innerBody) hdim
      (F.closureShade.outerBody j) hsubClosed (by
        change ConvexSpaceBody.IsFrostmanIn (F.fiber j)
          (fun i ↦ (F.innerBody i).toConvexSpaceBody) (F.outerBody j) C
        exact hFrostman j hj) hneClosed hVposClosed hagg hunifClosed hNClosed (by
          intro i _
          exact F.closureShade_isClosed_shade i))
    (fun hFrostman ↦ lambdaInducedSingleWAggregate_of_thickenedFrostman
      (s := F.closureShade.fiber j) (V := F.closureShade.innerBody) hdim
      (F.closureShade.outerBody j) hsubClosed (by
        change Kakeya.maxDensity (F.fiber j) (fun i =>
            (F.innerBody i).toConvexSpaceBody.cthickening (2 * (F.outerBody j).scale)) *
            volume (F.outerBody j).carrier ≤
          C * ∑ i ∈ F.fiber j,
            volume ((F.innerBody i).toConvexSpaceBody.cthickening
              (2 * (F.outerBody j).scale)).carrier
        exact hFrostman j hj)
      hneClosed hVposClosed hagg hunifClosed hNClosed (by
        intro i _
        exact F.closureShade_isClosed_shade i))
  have h := hclosed
  rw [show F.closureShade.innerBody =
    (fun i ↦ (F.innerBody i).closureShade.toShadedBody) by rfl,
    shade_inducedShading_closureShade] at h
  simpa only [FactorFamily.closureShade_outerBody,
    FactorFamily.closureShade_fiber] using h

open Classical in
/-- Aggregate measurable form of GWZ Lemma 5.9 under the ordinary fibrewise Frostman
hypothesis. -/
lemma aggregateFullnessForInducedShading_of_measurable {C : ENNReal} {N : ℕ}
    (F : FactorFamily E ι κ) (hdim : Module.finrank ℝ E = 3)
    (hshape : F.InnerHasSimilarShape 2)
    (hFrostman : F.HasFrostmanFibers C)
    (hne : ∀ j ∈ F.outerSet, (F.fiber j).Nonempty)
    (hVpos : ∀ i ∈ F.innerSet, volume (F.innerBody i).carrier ≠ 0)
    (lam : κ → ENNReal)
    (hlam : ∀ j ∈ F.outerSet,
      lam j * (∑ i ∈ F.fiber j, volume (F.innerBody i).carrier) ≤
        ∑ i ∈ F.fiber j, volume (F.innerBody i).shade)
    (hN : ∀ j ∈ F.outerSet, ∀ i ∈ F.fiber j,
      volume (F.outerBody j).carrier ≤ 2 ^ N * volume (F.innerBody i).carrier) :
    ∀ j ∈ F.outerSet,
      C⁻¹ * (lam j) ^ 2 *
          volume ((F.outerBody j).cthickening
            (Metric.thickness ℝ (F.outerBody j).carrier
              (Module.finrank ℝ E - 1))).carrier
        ≤ (lambdaInducedSingleWUniform.C : ENNReal) * ((N : ENNReal) + 1) *
          volume (inducedShading (s := F.fiber j) (V := F.innerBody)
            (F.outerBody j)).shade :=
  aggregateFullnessForInducedShading_of_measurable_aux F hdim hshape (Or.inl hFrostman)
    hne hVpos lam hlam hN

open Classical in
/-- Aggregate measurable form of GWZ Lemma 5.9 under GWZ Remark 5.3's fibrewise Frostman
hypothesis for the inner carriers thickened at the shortest outer scale. -/
lemma aggregateFullnessForInducedShading_of_measurable_of_thickenedFrostman
    {C : ENNReal} {N : ℕ}
    (F : FactorFamily E ι κ) (hdim : Module.finrank ℝ E = 3)
    (hshape : F.InnerHasSimilarShape 2)
    (hFrostman : F.HasThickenedFrostmanFibers C)
    (hne : ∀ j ∈ F.outerSet, (F.fiber j).Nonempty)
    (hVpos : ∀ i ∈ F.innerSet, volume (F.innerBody i).carrier ≠ 0)
    (lam : κ → ENNReal)
    (hlam : ∀ j ∈ F.outerSet,
      lam j * (∑ i ∈ F.fiber j, volume (F.innerBody i).carrier) ≤
        ∑ i ∈ F.fiber j, volume (F.innerBody i).shade)
    (hN : ∀ j ∈ F.outerSet, ∀ i ∈ F.fiber j,
      volume (F.outerBody j).carrier ≤ 2 ^ N * volume (F.innerBody i).carrier) :
    ∀ j ∈ F.outerSet,
      C⁻¹ * (lam j) ^ 2 *
          volume ((F.outerBody j).cthickening
            (Metric.thickness ℝ (F.outerBody j).carrier
              (Module.finrank ℝ E - 1))).carrier
        ≤ (lambdaInducedSingleWUniform.C : ENNReal) * ((N : ENNReal) + 1) *
          volume (inducedShading (s := F.fiber j) (V := F.innerBody)
            (F.outerBody j)).shade :=
  aggregateFullnessForInducedShading_of_measurable_aux F hdim hshape (Or.inr hFrostman)
    hne hVpos lam hlam hN

end ShadedBody

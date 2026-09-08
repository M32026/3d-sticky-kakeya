/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Mathlib.ENNReal
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Convex.Join
public import Mathlib.Geometry.Euclidean.Projection
public import Mathlib.Geometry.Euclidean.Volume.Measure

/-!
# Simplex
-/

@[expose] public section

namespace Metric

section FiniteDimensional

open Metric AffineSubspace Set MeasureTheory InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The multiplicative constant in `Metric.lt_volume_convexHull`. -/
@[nolint defsWithUnderscore]
noncomputable abbrev lt_volume_convexHull.c (dim : ℕ) : NNReal :=
  (dim.factorial : NNReal)⁻¹

theorem lt_volume_convexHull.c_pos (dim : ℕ) : 0 < lt_volume_convexHull.c dim := by
  rw [pos_iff_ne_zero, ne_eq, inv_eq_zero, Nat.cast_eq_zero]
  exact Nat.factorial_pos dim |>.ne'

/-- The cone cross-section integral: `∫₀ʰ (1 - x/h)^m dx = h/(m+1)`, in `ENNReal` form. -/
private lemma lintegral_Icc_one_sub_div_pow {h : ℝ} (hh : 0 < h) (m : ℕ) :
    ∫⁻ x in Set.Icc (0 : ℝ) h, ENNReal.ofReal ((1 - x / h) ^ m) = ENNReal.ofReal (h / (m + 1)) := by
  have hh0 : h ≠ 0 := hh.ne'
  have hcont : Continuous fun x : ℝ => (1 - x / h) ^ m := by fun_prop
  have hcongr : ∀ x : ℝ, (1 - x / h) ^ m = (h - x) ^ m / h ^ m := fun x => by
    rw [← div_pow]; congr 1; field_simp
  have hint : ∫ x in Set.Icc (0 : ℝ) h, (1 - x / h) ^ m = h / (m + 1) := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hh.le,
      intervalIntegral.integral_congr (g := fun x => (h - x) ^ m / h ^ m) (fun x _ => hcongr x),
      intervalIntegral.integral_div, intervalIntegral.integral_comp_sub_left (fun x => x ^ m) h,
      sub_self, sub_zero, integral_pow, zero_pow (Nat.succ_ne_zero m)]
    field_simp
    ring
  rw [← ofReal_integral_eq_lintegral_ofReal (hcont.integrableOn_Icc), hint]
  refine (ae_restrict_iff' measurableSet_Icc).mpr (Filter.Eventually.of_forall fun x hx => ?_)
  exact pow_nonneg (by rw [sub_nonneg, div_le_one hh]; exact hx.2) m

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Cross-section of a cone: slicing `convexHull (insert a s)` by the affine hyperplane on which the
linear functional `⟨v, · - p₀⟩` takes the value `x` (with the base `s` at level `0` and the apex `a`
at level `h > 0`) yields the homothety image of the base hull with ratio `1 - x/h`. -/
private lemma convexHull_insert_inter_setOf_inner {a p₀ v : E} {s : Set E} (hs : s.Nonempty)
    (hbase : ∀ b ∈ s, inner ℝ v (b - p₀) = (0 : ℝ))
    {h : ℝ} (hh : 0 < h) (hapex : inner ℝ v (a - p₀) = h)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) h) :
    convexHull ℝ (insert a s) ∩ {y | inner ℝ v (y - p₀) = x}
      = ⇑(AffineMap.homothety a (1 - x / h)) '' convexHull ℝ s := by
  have hh0 : h ≠ 0 := hh.ne'
  -- the level functional vanishes on the whole base hull
  have hbase' : ∀ b ∈ convexHull ℝ s, inner ℝ v (b - p₀) = (0 : ℝ) := by
    have hconv : Convex ℝ {z : E | inner ℝ v (z - p₀) = (0 : ℝ)} := by
      intro y1 h1 y2 h2 t1 t2 _ _ hsum
      simp only [Set.mem_setOf_eq] at h1 h2 ⊢
      have hcomb : t1 • (y1 - p₀) + t2 • (y2 - p₀) = t1 • y1 + t2 • y2 - p₀ := by
        rw [smul_sub, smul_sub,
          show t1 • y1 - t1 • p₀ + (t2 • y2 - t2 • p₀)
            = t1 • y1 + t2 • y2 - (t1 • p₀ + t2 • p₀) from by abel,
          ← add_smul, hsum, one_smul]
      rw [← hcomb, inner_add_right, real_inner_smul_right, real_inner_smul_right, h1, h2]
      ring
    exact fun b hb => convexHull_min (fun z hz => hbase z hz) hconv hb
  -- the level of a point `lineMap a b t` (with `b` at level `0`)
  have hlevel : ∀ b : E, inner ℝ v (b - p₀) = (0 : ℝ) → ∀ t : ℝ,
      inner ℝ v (AffineMap.lineMap a b t - p₀) = h * (1 - t) := by
    intro b hb t
    have hba : inner ℝ v (b - a) = -h := by
      rw [show b - a = (b - p₀) - (a - p₀) from by abel, inner_sub_right, hb, hapex]; ring
    rw [show AffineMap.lineMap a b t - p₀ = t • (b - a) + (a - p₀) from by
          rw [AffineMap.lineMap_apply]; simp only [vsub_eq_sub, vadd_eq_add]; abel,
      inner_add_right, real_inner_smul_right, hba, hapex]; ring
  set c : ℝ := 1 - x / h with hc_def
  have hcIcc : c ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨?_, ?_⟩
    · rw [hc_def, sub_nonneg, div_le_one hh]; exact hx.2
    · have : 0 ≤ x / h := div_nonneg hx.1 hh.le; rw [hc_def]; linarith
  have hcx : h * (1 - c) = x := by rw [hc_def]; field_simp; ring
  refine Set.Subset.antisymm (fun y hy => ?_) (fun y hy => ?_)
  · -- `⊆`
    obtain ⟨hyhull, hylev⟩ := hy
    rw [Set.mem_setOf_eq] at hylev
    rw [convexHull_insert hs, mem_convexJoin] at hyhull
    obtain ⟨a', ha', b, hb, hyseg⟩ := hyhull
    rw [Set.mem_singleton_iff] at ha'; subst ha'
    rw [segment_eq_image_lineMap] at hyseg
    obtain ⟨t, _, rfl⟩ := hyseg
    have htx : h * (1 - t) = x := (hlevel b (hbase' b hb) t).symm.trans hylev
    have htc : t = c := by
      have := mul_left_cancel₀ hh0 (htx.trans hcx.symm); linarith
    exact ⟨b, hb, by rw [AffineMap.homothety_eq_lineMap, htc]⟩
  · -- `⊇`
    obtain ⟨b, hb, rfl⟩ := hy
    refine ⟨?_, ?_⟩
    · rw [convexHull_insert hs, AffineMap.homothety_eq_lineMap]
      refine segment_subset_convexJoin (Set.mem_singleton_iff.mpr rfl) hb ?_
      rw [segment_eq_image_lineMap]
      exact ⟨c, hcIcc, rfl⟩
    · rw [Set.mem_setOf_eq, AffineMap.homothety_eq_lineMap, hlevel b (hbase' b hb) c, hcx]

/-- The cone-volume recursion: in an `(m+1)`-dimensional space, the volume of a cone with apex `a`
over a base `s` (lying in a hyperplane at distance `h > 0` orthogonal to the unit vector `v`) is
`h/(m+1)` times the `m`-dimensional measure of the base hull. -/
private lemma μHE_convexHull_insert_eq {m : ℕ} (hfr : Module.finrank ℝ E = m + 1)
    {a p₀ v : E} {s : Set E} (hs_ne : s.Nonempty)
    (hs_meas : MeasurableSet (convexHull ℝ (insert a s)))
    (hbase : ∀ b ∈ s, inner ℝ v (b - p₀) = (0 : ℝ)) (hv : ‖v‖ = 1)
    {h : ℝ} (hh : 0 < h) (hapex : inner ℝ v (a - p₀) = h) :
    μHE[m + 1] (convexHull ℝ (insert a s))
      = ENNReal.ofReal (h / (m + 1)) * μHE[m] (convexHull ℝ s) := by
  have hvne : v ≠ 0 := fun h0 => by simp [h0] at hv
  set M := μHE[m] (convexHull ℝ s) with hM
  -- the slice hyperplane is the level set `⟨v, · - p₀⟩ = x`
  have hhyp : ∀ x : ℝ, (↑(AffineSubspace.mk' (x • v +ᵥ p₀) (ℝ ∙ v)ᗮ) : Set E)
      = {y | inner ℝ v (y - p₀) = x} := by
    intro x
    ext y
    rw [SetLike.mem_coe, AffineSubspace.mem_mk',
      Submodule.mem_orthogonal_singleton_iff_inner_right, Set.mem_setOf_eq, vsub_eq_sub,
      show y - (x • v +ᵥ p₀) = (y - p₀) - x • v from by rw [vadd_eq_add]; abel,
      inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hv, one_pow, mul_one,
      sub_eq_zero]
  -- affine expansion of the level functional on a binary combination
  have hlevel_comb : ∀ (y1 y2 : E) (t1 t2 : ℝ), t1 + t2 = 1 →
      inner ℝ v (t1 • y1 + t2 • y2 - p₀) = t1 * inner ℝ v (y1 - p₀) + t2 * inner ℝ v (y2 - p₀) := by
    intro y1 y2 t1 t2 hsum
    rw [show t1 • y1 + t2 • y2 - p₀ = t1 • (y1 - p₀) + t2 • (y2 - p₀) from by
        rw [smul_sub, smul_sub,
          show t1 • y1 - t1 • p₀ + (t2 • y2 - t2 • p₀)
            = t1 • y1 + t2 • y2 - (t1 • p₀ + t2 • p₀) from by abel, ← add_smul, hsum, one_smul],
      inner_add_right, real_inner_smul_right, real_inner_smul_right]
  -- the level functional on the cone lies in `[0, h]`
  have hlevels : ∀ y ∈ convexHull ℝ (insert a s), inner ℝ v (y - p₀) ∈ Set.Icc (0 : ℝ) h := by
    have hsub : insert a s ⊆ {y : E | inner ℝ v (y - p₀) ∈ Set.Icc (0 : ℝ) h} := by
      rintro z hz
      rcases hz with rfl | hz
      · rw [Set.mem_setOf_eq, hapex]; exact ⟨hh.le, le_refl h⟩
      · rw [Set.mem_setOf_eq, hbase z hz]; exact ⟨le_refl 0, hh.le⟩
    have hconv : Convex ℝ {y : E | inner ℝ v (y - p₀) ∈ Set.Icc (0 : ℝ) h} := by
      intro y1 h1 y2 h2 t1 t2 ht1 ht2 hsum
      simp only [Set.mem_setOf_eq] at h1 h2 ⊢
      rw [hlevel_comb y1 y2 t1 t2 hsum]
      refine ⟨?_, ?_⟩
      · have := mul_nonneg ht1 h1.1; have := mul_nonneg ht2 h2.1; linarith
      · nlinarith [mul_le_mul_of_nonneg_left h1.2 ht1, mul_le_mul_of_nonneg_left h2.2 ht2]
    exact fun y hy => convexHull_min hsub hconv hy
  -- the measure of each (non-degenerate) slice
  have hhom : ∀ x : ℝ, x ∈ Set.Ico (0 : ℝ) h →
      μHE[m] (⇑(AffineMap.homothety a (1 - x / h)) '' convexHull ℝ s)
        = ENNReal.ofReal ((1 - x / h) ^ m) * M := by
    intro x hx
    have hcpos : 0 < 1 - x / h := by
      have : x / h < 1 := (div_lt_one hh).mpr hx.2; linarith
    rw [euclideanHausdorffMeasure_homothety_image m a hcpos.ne' (convexHull ℝ s), ← hM,
      ENNReal.smul_def, smul_eq_mul, ENNReal.coe_pow,
      show (‖1 - x / h‖₊ : ENNReal) = ENNReal.ofReal (1 - x / h) from by
        rw [← enorm_eq_nnnorm]; exact Real.enorm_eq_ofReal hcpos.le,
      ← ENNReal.ofReal_pow hcpos.le]
  -- the integrand equals the indicator a.e.
  have hae : (fun x => μHE[m] (convexHull ℝ (insert a s) ∩
        ↑(AffineSubspace.mk' (x • v +ᵥ p₀) (ℝ ∙ v)ᗮ)))
      =ᵐ[volume] Set.indicator (Set.Ico 0 h)
        (fun x => ENNReal.ofReal ((1 - x / h) ^ m) * M) := by
    have hne : ∀ᵐ x : ℝ ∂volume, x ≠ h := by rw [ae_iff]; simp
    filter_upwards [hne] with x hx
    rw [hhyp x]
    by_cases hxi : x ∈ Set.Ico (0 : ℝ) h
    · rw [Set.indicator_of_mem hxi,
        convexHull_insert_inter_setOf_inner hs_ne hbase hh hapex ⟨hxi.1, hxi.2.le⟩, hhom x hxi]
    · have hempty : convexHull ℝ (insert a s) ∩ {y | inner ℝ v (y - p₀) = x} = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro y ⟨hyC, hyl⟩
        rw [Set.mem_setOf_eq] at hyl
        obtain ⟨hl0, hlh⟩ := hlevels y hyC
        rw [hyl] at hl0 hlh
        exact hxi ⟨hl0, lt_of_le_of_ne hlh hx⟩
      rw [Set.indicator_of_notMem hxi, hempty, measure_empty]
  -- assemble via the slice lemma and the cone integral
  have hv1 : ‖v‖ₑ = 1 := by
    rw [enorm_eq_nnnorm, show ‖v‖₊ = 1 from by rw [← NNReal.coe_inj]; simpa using hv,
      ENNReal.coe_one]
  rw [← hfr, EuclideanGeometry.euclideanHausdorffMeasure_eq_lintegral p₀ hvne hs_meas, hv1, one_mul]
  simp only [hfr, Nat.add_sub_cancel]
  rw [lintegral_congr_ae hae, lintegral_indicator measurableSet_Ico,
    lintegral_mul_const _ (by fun_prop), MeasureTheory.setLIntegral_congr Ico_ae_eq_Icc,
    lintegral_Icc_one_sub_div_pow hh m]

omit [FiniteDimensional ℝ E] in
/-- Transport of the simplex data along an affine isometry `Φ : F →ᵃⁱ[ℝ] E`: the Euclidean
Hausdorff measure of the image hull equals the intrinsic measure in `F`, and each cone height is
preserved. This packages the dimension-drop step of the induction, so the caller only has to build
the isometry into the relevant subspace and convert `μHE[m]` to `volume` there. -/
private lemma μHE_convexHull_affineIsometry_image
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
    {m : ℕ} (Φ : F →ᵃⁱ[ℝ] E) (r : Fin (m + 1) → F) :
    μHE[m] (convexHull ℝ (Set.range (⇑Φ ∘ r))) = μHE[m] (convexHull ℝ (Set.range r)) ∧
      ∀ i : Fin m, infEDist ((⇑Φ ∘ r) i.succ) ↑(affineSpan ℝ ((⇑Φ ∘ r) '' Set.Iic i.castSucc))
        = infEDist (r i.succ) ↑(affineSpan ℝ (r '' Set.Iic i.castSucc)) := by
  have hcoe : (⇑Φ : F → E) = ⇑Φ.toAffineMap := rfl
  refine ⟨?_, fun i => ?_⟩
  · rw [Set.range_comp,
      show convexHull ℝ (⇑Φ '' Set.range r) = ⇑Φ '' convexHull ℝ (Set.range r) from by
        rw [hcoe, ← AffineMap.image_convexHull],
      Φ.isometry.euclideanHausdorffMeasure_image]
  · have himg : (⇑Φ ∘ r) '' Set.Iic i.castSucc = ⇑Φ '' (r '' Set.Iic i.castSucc) :=
      Set.image_comp _ _ _
    rw [Function.comp_apply, himg, hcoe, ← AffineSubspace.map_span, AffineSubspace.coe_map,
      ← hcoe, Metric.infEDist_image Φ.isometry]

/-- The exact value of the volume of a simplex: `(finrank!)⁻¹` times the product of the heights
`infEDist (p i.succ) (affineSpan {p 0, …, p i})`. This holds for every configuration of points,
including degenerate ones (where some height, and the volume, vanish). -/
theorem volume_convexHull_eq {n : ℕ} (hn : n = Module.finrank ℝ E) (p : Fin (n + 1) → E) :
    volume (convexHull ℝ (range p)) = lt_volume_convexHull.c (Module.finrank ℝ E) *
      ∏ i : Fin n, infEDist (p i.succ) ↑(affineSpan ℝ (p '' Set.Iic i.castSucc)) := by
  induction n generalizing E with
  | zero =>
    -- `E` is `0`-dimensional, hence a subsingleton: the convex hull is everything, of volume `1`.
    have hfr : Module.finrank ℝ E = 0 := hn.symm
    haveI : Subsingleton E := Module.finrank_zero_iff.1 hfr
    have huniv : convexHull ℝ (range p) = Set.univ :=
      Subsingleton.eq_univ_of_nonempty ⟨p 0, subset_convexHull ℝ _ (Set.mem_range_self 0)⟩
    have hc0 : (lt_volume_convexHull.c 0 : ENNReal) = 1 := by simp [lt_volume_convexHull.c]
    have hvol : volume (Set.univ : Set E) = 1 := by
      have hsub : (Set.univ : Set E) = {p 0} :=
        (Subsingleton.eq_univ_of_nonempty (Set.singleton_nonempty (p 0))).symm
      rw [← InnerProductSpace.euclideanHausdorffMeasure_eq_volume, hfr, hsub,
        MeasureTheory.Measure.euclideanHausdorffMeasure_zero,
        MeasureTheory.Measure.hausdorffMeasure_zero_singleton]
    rw [huniv, hfr, Fin.prod_univ_zero, mul_one, hc0, hvol]
  | succ m ih =>
    set a : E := p (Fin.last (m + 1)) with ha
    set q : Fin (m + 1) → E := Fin.init p with hq
    have hrange : Set.range p = insert a (Set.range q) := by
      rw [ha, hq, ← Fin.range_snoc, Fin.snoc_init_self]
    -- `castSucc` maps initial segments to initial segments
    have hcast : ∀ j : Fin (m + 1), Fin.castSucc '' Set.Iic j = Set.Iic j.castSucc := by
      intro j
      ext k
      simp only [Set.mem_image, Set.mem_Iic, Fin.le_def, Fin.val_castSucc]
      constructor
      · rintro ⟨l, hl, rfl⟩; simpa [Fin.val_castSucc] using hl
      · intro hk
        have hjm : (j : ℕ) ≤ m := Nat.lt_succ_iff.mp j.isLt
        exact ⟨⟨(k : ℕ), by omega⟩, by simpa using hk, by apply Fin.ext; simp⟩
    -- the prefix point sets of `p` (through one more index) match those of the base `q`
    have himg : ∀ j : Fin (m + 1), p '' Set.Iic j.castSucc = q '' Set.Iic j := by
      intro j
      rw [hq, Fin.init_def, show (fun i => p i.castSucc) = p ∘ Fin.castSucc from rfl,
        Set.image_comp, hcast j]
    -- splitting the last height (the cone height) off the product
    have hsplit : (∏ i : Fin (m + 1), infEDist (p i.succ) ↑(affineSpan ℝ (p '' Set.Iic i.castSucc)))
        = (∏ i : Fin m, infEDist (q i.succ) ↑(affineSpan ℝ (q '' Set.Iic i.castSucc)))
          * infEDist a ↑(affineSpan ℝ (Set.range q)) := by
      rw [Fin.prod_univ_castSucc]
      congr 1
      · refine Finset.prod_congr rfl (fun i _ => ?_)
        rw [Fin.succ_castSucc, himg i.castSucc]
        congr 1
      · rw [Fin.succ_last, himg (Fin.last m),
          show Set.Iic (Fin.last m) = Set.univ from Set.eq_univ_of_forall fun k => Fin.le_last k,
          Set.image_univ, ← ha]
    -- the base measure, evaluated by the induction hypothesis through an isometry
    have htrans : μHE[m] (convexHull ℝ (Set.range q))
        = lt_volume_convexHull.c m
          * ∏ i : Fin m, infEDist (q i.succ) ↑(affineSpan ℝ (q '' Set.Iic i.castSucc)) := by
      set A0 := affineSpan ℝ (Set.range q) with hA0
      -- the base spans an `≤ m`-dimensional affine subspace, so a unit normal exists
      have hdirlt : Module.finrank ℝ A0.direction < Module.finrank ℝ E := by
        rw [hA0, direction_affineSpan, ← hn]
        exact lt_of_le_of_lt (finrank_vectorSpan_range_le ℝ q (Fintype.card_fin _))
          (Nat.lt_succ_self m)
      have hpos : 0 < Module.finrank ℝ A0.directionᗮ := by
        have hsum := Submodule.finrank_add_finrank_orthogonal (K := A0.direction)
        omega
      have hne : A0.directionᗮ ≠ ⊥ := fun h => by
        rw [h, finrank_bot] at hpos; exact lt_irrefl 0 hpos
      obtain ⟨v, hvmem, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
      have hfinW : Module.finrank ℝ ((ℝ ∙ v)ᗮ) = m := by
        have h1 := Submodule.finrank_add_finrank_orthogonal (K := (ℝ ∙ v))
        rw [finrank_span_singleton hv0, ← hn] at h1
        omega
      -- each base difference `q i - q 0` lies in `(ℝ ∙ v)ᗮ`
      have hperp : ∀ i : Fin (m + 1), q i - q 0 ∈ (ℝ ∙ v)ᗮ := by
        intro i
        rw [Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_comm]
        exact (Submodule.mem_orthogonal _ _).mp hvmem (q i - q 0)
          (AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ _ (Set.mem_range_self i))
            (subset_affineSpan ℝ _ (Set.mem_range_self 0)))
      set q'' : Fin (m + 1) → (ℝ ∙ v)ᗮ := fun i => ⟨q i - q 0, hperp i⟩ with hq''
      -- the affine isometry carrying the model points back into `E`
      set Ψ : (ℝ ∙ v)ᗮ →ᵃⁱ[ℝ] E :=
        (AffineIsometryEquiv.constVAdd ℝ E (q 0)).toAffineIsometry.comp
          ((ℝ ∙ v)ᗮ).subtypeₗᵢ.toAffineIsometry with hΨ
      have hΨq : ∀ i, Ψ (q'' i) = q i := by
        intro i
        rw [hΨ, AffineIsometry.coe_comp, Function.comp_apply,
          AffineIsometryEquiv.coe_toAffineIsometry, LinearIsometry.coe_toAffineIsometry,
          Submodule.coe_subtypeₗᵢ, AffineIsometryEquiv.coe_constVAdd]
        change q 0 +ᵥ ((q'' i : (ℝ ∙ v)ᗮ) : E) = q i
        rw [hq'']
        change q 0 +ᵥ (q i - q 0) = q i
        rw [vadd_eq_add]; abel
      have hcomp : ⇑Ψ ∘ q'' = q := funext hΨq
      obtain ⟨hμ, hheights⟩ := μHE_convexHull_affineIsometry_image Ψ q''
      rw [hcomp] at hμ hheights
      rw [hμ, show (μHE[m] : Measure ((ℝ ∙ v)ᗮ)) = volume from
          hfinW ▸ InnerProductSpace.euclideanHausdorffMeasure_eq_volume, ih hfinW.symm q'', hfinW]
      congr 1
      exact Finset.prod_congr rfl fun i _ => (hheights i).symm
    rw [hrange, ← InnerProductSpace.euclideanHausdorffMeasure_eq_volume, ← hn, hsplit]
    set A := affineSpan ℝ (Set.range q) with hAdef
    haveI : Nonempty A := ⟨⟨q 0, subset_affineSpan ℝ _ (Set.mem_range_self 0)⟩⟩
    haveI : A.direction.HasOrthogonalProjection := inferInstance
    have hμHE : (μHE[m + 1] : Measure E) = volume := by
      rw [hn]; exact InnerProductSpace.euclideanHausdorffMeasure_eq_volume
    by_cases hdeg : infEDist a (A : Set E) = 0
    · -- degenerate: the apex lies in the base span, so the whole simplex is lower-dimensional
      rw [hdeg, mul_zero, mul_zero, hμHE]
      have ha_mem : a ∈ (A : Set E) :=
        (Metric.mem_iff_infEDist_zero_of_closed A.closed_of_finiteDimensional).mpr hdeg
      have hsub : convexHull ℝ (insert a (Set.range q)) ⊆ (A : Set E) :=
        convexHull_min (Set.insert_subset ha_mem (subset_affineSpan ℝ _)) A.convex
      have hAne : A ≠ ⊤ := by
        intro hAtop
        have h1 : Module.finrank ℝ A.direction ≤ m := by
          rw [hAdef, direction_affineSpan]
          exact finrank_vectorSpan_range_le ℝ q (Fintype.card_fin (m + 1))
        rw [hAtop, AffineSubspace.direction_top, finrank_top] at h1
        omega
      exact measure_mono_null hsub (MeasureTheory.Measure.addHaar_affineSubspace volume A hAne)
    · -- non-degenerate: build the unit normal `v` and height from the orthogonal projection
      set foot : E := (EuclideanGeometry.orthogonalProjection A a : E) with hfoot
      have hfoot_mem : foot ∈ (A : Set E) := EuclideanGeometry.orthogonalProjection_mem a
      set w : E := a - foot with hw
      have hw_orth : w ∈ A.directionᗮ :=
        EuclideanGeometry.vsub_orthogonalProjection_mem_direction_orthogonal A a
      have hane : infEDist a (A : Set E) ≠ ⊤ :=
        Metric.infEDist_ne_top ⟨q 0, subset_affineSpan ℝ _ (Set.mem_range_self 0)⟩
      have hinfeq : infEDist a (A : Set E) = ENNReal.ofReal ‖w‖ := by
        rw [← ENNReal.ofReal_toReal hane]
        congr 1
        rw [show (infEDist a (A : Set E)).toReal = Metric.infDist a (A : Set E) from rfl,
          ← EuclideanGeometry.dist_orthogonalProjection_eq_infDist A a, dist_eq_norm, ← hfoot, ← hw]
      have hwne : w ≠ 0 := by
        intro hw0
        exact hdeg (by rw [hinfeq, hw0, norm_zero, ENNReal.ofReal_zero])
      have hhpos : 0 < ‖w‖ := norm_pos_iff.mpr hwne
      set v : E := ‖w‖⁻¹ • w with hv
      have hvnorm : ‖v‖ = 1 := by
        rw [hv, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hhpos),
          inv_mul_cancel₀ hhpos.ne']
      have hbase : ∀ b ∈ Set.range q, inner ℝ v (b - foot) = (0 : ℝ) := by
        intro b hb
        have hbA : b ∈ (A : Set E) := subset_affineSpan ℝ _ hb
        have hbdir : b - foot ∈ A.direction := AffineSubspace.vsub_mem_direction hbA hfoot_mem
        rw [hv, real_inner_smul_left, Submodule.inner_left_of_mem_orthogonal hbdir hw_orth,
          mul_zero]
      have hapex : inner ℝ v (a - foot) = ‖w‖ := by
        rw [hv, real_inner_smul_left, ← hw, real_inner_self_eq_norm_sq, pow_two, ← mul_assoc,
          inv_mul_cancel₀ hhpos.ne', one_mul]
      have hmeas : MeasurableSet (convexHull ℝ (insert a (Set.range q))) :=
        (((Set.finite_range q).insert a).isCompact_convexHull ℝ).measurableSet
      rw [μHE_convexHull_insert_eq hn.symm ⟨q 0, Set.mem_range_self 0⟩ hmeas hbase hvnorm hhpos
        hapex, htrans, hinfeq]
      -- pure `ENNReal` arithmetic with the factorial constants
      have hco : ∀ k : ℕ, (↑(lt_volume_convexHull.c k) : ENNReal)
          = ENNReal.ofReal ((Nat.factorial k : ℝ)⁻¹) := by
        intro k
        rw [show (lt_volume_convexHull.c k : NNReal) = (Nat.factorial k : NNReal)⁻¹ from rfl,
          ← ENNReal.ofReal_coe_nnreal, NNReal.coe_inv, NNReal.coe_natCast]
      have hconst : ENNReal.ofReal (‖w‖ / (m + 1)) * ↑(lt_volume_convexHull.c m)
          = ↑(lt_volume_convexHull.c (m + 1)) * ENNReal.ofReal ‖w‖ := by
        rw [hco, hco, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [Nat.factorial_succ]
        have hm : (0 : ℝ) < (Nat.factorial m : ℝ) := by positivity
        push_cast
        field_simp
      rw [show ENNReal.ofReal (‖w‖ / (m + 1))
            * (↑(lt_volume_convexHull.c m)
              * ∏ i : Fin m, infEDist (q i.succ) ↑(affineSpan ℝ (q '' Set.Iic i.castSucc)))
          = (ENNReal.ofReal (‖w‖ / (m + 1)) * ↑(lt_volume_convexHull.c m))
              * ∏ i : Fin m, infEDist (q i.succ) ↑(affineSpan ℝ (q '' Set.Iic i.castSucc)) from by
          ring, hconst]
      ring

theorem lt_volume_convexHull [Nontrivial E] {n : ℕ} (hn : n = Module.finrank ℝ E)
    {r : Fin n → ENNReal} {p : Fin (n + 1) → E}
    (hr : ∀ i, r i < infEDist (p i.succ) ↑(affineSpan ℝ (p '' Set.Iic i.castSucc))) :
    lt_volume_convexHull.c (Module.finrank ℝ E) * ∏ i, r i < volume (convexHull ℝ (range p)) := by
  have hpos : 0 < n := hn ▸ Module.finrank_pos
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hpos
  -- abbreviation for the heights
  set h : Fin n → ENNReal :=
    fun i : Fin n => infEDist (p i.succ) ↑(affineSpan ℝ (p '' Set.Iic i.castSucc)) with hh
  -- each height is nonzero (it bounds `r i` from above) and finite (the span is nonempty)
  have hmem : ∀ i : Fin n, p i.castSucc ∈ (affineSpan ℝ (p '' Set.Iic i.castSucc) : Set E) :=
    fun i => subset_affineSpan ℝ _ (Set.mem_image_of_mem p Set.self_mem_Iic)
  have htop : ∀ i, h i ≠ ⊤ := fun i => infEDist_ne_top ⟨_, hmem i⟩
  have h0 : ∀ i, h i ≠ 0 := fun i => (zero_le.trans_lt (hr i)).ne'
  rw [volume_convexHull_eq hn p]
  exact ENNReal.mul_lt_mul_right (by exact_mod_cast (lt_volume_convexHull.c_pos _).ne')
    ENNReal.coe_ne_top (ENNReal.prod_lt_prod_of_lt hr h0 htop)

end FiniteDimensional

end Metric

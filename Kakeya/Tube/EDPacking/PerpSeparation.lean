/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Tube.EDPacking.MidpointSeparation

/-!
# ED implies perp-projection δ-separation and pointwise multiplicity bound

For tubes within a direction class, ED forces pairwise δ-separated perpendicular
midpoint offsets, yielding a pointwise multiplicity bound.
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped InnerProductSpace RealInnerProductSpace

namespace Kakeya

noncomputable section
variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E]

/-! ### ED ⟹ perp-projection δ-separation; pointwise multiplicity ≤ C_n

Position-count infrastructure for the convex-projection-Fubini double
counting in `badAgainstSet_count_le_of_ED_thinBox`
(`Kakeya/Tube/EDPacking/BadAgainstSet.lean`).

**Geometric content.** Within a single direction class (tubes whose
directions all lie inside a common cap), ED forces the *perpendicular*
midpoint offsets to be pairwise δ-separated. Equivalently, the
projection of midpoints onto the orthogonal complement of the class
direction is δ-separated. This yields a pointwise multiplicity bound:
for any `p ∈ E`, the number of ED δ-tubes whose carriers contain `p`
and whose directions lie in a single δ-cap is bounded by a
dimension-only constant `C_n`.

This is the position-count input to the volume double-counting
argument: for each direction class, `∑ᵢ vol(Tᵢ ∩ K) ≤ C_n · vol(K)`,
which combined with the bad-tube hypothesis
`vol(Tᵢ ∩ K) ≥ c · vol(Tᵢ)` produces `|Bad_e| ≤ C_n · M / c`.

**Inputs used.** `ed_midpoint_perp_separation` from
`Kakeya/Tube/EDPacking/MidpointSeparation.lean` (the δ-perp gap
under direction-class assumption) is the workhorse; this file lifts
it to the multiplicity / packing form consumed by the position-count
argument. -/

/-- **Abstract packing bound in an `n`-dimensional Euclidean space.**

For a finite set in an `n`-dim inner-product space whose pairwise
separation is `≥ c` and whose elements all lie within radius `R` of a
common centre `q`, the cardinality is bounded by a dimension-only
constant `N = N(n, R, c)`. Standard ball packing (Besicovitch-type)
bound after rescaling. The witness `N` is hoisted outside the
universal binders. -/
private lemma packing_bound_aux
    (n : ℕ) (R c : ℝ) (_hR : 0 < R) (_hc : 0 < c) :
    ∃ N : ℕ, 0 < N ∧
      ∀ {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
        [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
        [ProperSpace F]
        (_hF : Module.finrank ℝ F = n)
        {ι : Type*} (s : Finset ι) (f : ι → F) (q : F)
        (_hball : ∀ i ∈ s, ‖f i - q‖ ≤ R)
        (_hsep : (s : Set ι).Pairwise (fun i j => c ≤ ‖f i - f j‖)),
        s.card ≤ N := by
  classical
  refine ⟨⌈((2 * R + c) / c) ^ n⌉₊ + 1, by positivity, ?_⟩
  intro F _ _ _ _ _ _ hF ι s f q hball hsep
  have hρ_pos : (0 : ℝ) < c / 2 := by linarith only [_hc]
  have hRout_pos : (0 : ℝ) < R + c / 2 := by linarith only [_hR, _hc]
  have hdisj : Set.Pairwise (s : Set ι)
      (Function.onFun Disjoint fun i => Metric.ball (f i) (c / 2)) := by
    intro i hi j hj hij
    refine Metric.ball_disjoint_ball ?_
    rw [dist_eq_norm]
    linarith only [hsep hi hj hij]
  have hA_sub : (⋃ i ∈ s, Metric.ball (f i) (c / 2)) ⊆ Metric.ball q (R + c / 2) := by
    refine Set.iUnion₂_subset fun i hi x hx => ?_
    rw [Metric.mem_ball] at hx ⊢
    linarith only [dist_triangle x (f i) q, hx, hball i hi, dist_eq_norm (f i) q]
  have hvolA : volume (⋃ i ∈ s, Metric.ball (f i) (c / 2))
      = (s.card : ENNReal) * ENNReal.ofReal ((c / 2) ^ n) * volume (Metric.ball (0 : F) 1) := by
    rw [measure_biUnion_finset hdisj fun i _ => measurableSet_ball]
    simp only [(volume : Measure F).addHaar_ball_of_pos _ hρ_pos]
    rw [Finset.sum_const, nsmul_eq_mul, mul_assoc, hF]
  have hvol_ball : volume (Metric.ball q (R + c / 2))
      = ENNReal.ofReal ((R + c / 2) ^ n) * volume (Metric.ball (0 : F) 1) := by
    rw [(volume : Measure F).addHaar_ball_of_pos _ hRout_pos, hF]
  have hvol_le : (s.card : ENNReal) * ENNReal.ofReal ((c / 2) ^ n)
      * volume (Metric.ball (0 : F) 1)
      ≤ ENNReal.ofReal ((R + c / 2) ^ n) * volume (Metric.ball (0 : F) 1) := by
    rw [← hvolA, ← hvol_ball]
    exact measure_mono hA_sub
  have h_card_real : (s.card : ℝ) * (c / 2) ^ n ≤ (R + c / 2) ^ n := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      ((ENNReal.mul_le_mul_iff_left (measure_ball_pos volume (0 : F) zero_lt_one).ne'
        measure_ball_lt_top.ne).mp hvol_le)
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_pos hρ_pos n).le,
      ENNReal.toReal_ofReal (pow_pos hRout_pos n).le, ENNReal.toReal_natCast] at h
  have h_card : (s.card : ℝ) ≤ ((2 * R + c) / c) ^ n := by
    rw [show ((2 * R + c) / c : ℝ) = (R + c / 2) / (c / 2) from by
        rw [div_eq_div_iff (ne_of_gt _hc) (ne_of_gt hρ_pos)]; ring,
      div_pow, le_div_iff₀ (pow_pos hρ_pos n)]
    exact h_card_real
  have hfinal : (s.card : ℝ) ≤ ((⌈((2 * R + c) / c) ^ n⌉₊ + 1 : ℕ) : ℝ) := by
    push_cast
    linarith only [h_card, Nat.le_ceil (((2 * R + c) / c) ^ n)]
  exact_mod_cast hfinal

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E] in
/-- The perpendicular part of `v` relative to a unit vector `e` has norm at most `2‖v‖`. -/
private lemma norm_perp_le_two_mul_norm {e : E} (he : ‖e‖ = 1) (v : E) :
    ‖v - (inner ℝ v e : ℝ) • e‖ ≤ 2 * ‖v‖ := by
  have h1 : ‖(inner ℝ v e : ℝ) • e‖ = |(inner ℝ v e : ℝ)| := by
    rw [norm_smul, Real.norm_eq_abs, he, mul_one]
  have h2 : |(inner ℝ v e : ℝ)| ≤ ‖v‖ := by simpa [he] using abs_real_inner_le_norm v e
  refine (norm_sub_le _ _).trans ?_
  rw [h1]; linarith only [h2]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E] in
/-- The perpendicular part relative to a unit vector `e` kills `e`, so it is controlled by
the distance from `d` to the line `±e`. -/
private lemma norm_perp_le_two_mul_min {d e : E} (he : ‖e‖ = 1) :
    ‖d - (inner ℝ d e : ℝ) • e‖ ≤ 2 * min ‖d - e‖ ‖d + e‖ := by
  have he_inner : (inner ℝ e e : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, he]; norm_num
  rcases min_cases ‖d - e‖ ‖d + e‖ with ⟨hm, _⟩ | ⟨hm, _⟩
  · rw [hm, show d - (inner ℝ d e : ℝ) • e = (d - e) - (inner ℝ (d - e) e : ℝ) • e from by
      rw [inner_sub_left, he_inner, sub_smul, one_smul]; abel]
    exact norm_perp_le_two_mul_norm he _
  · rw [hm, show d - (inner ℝ d e : ℝ) • e = (d + e) - (inner ℝ (d + e) e : ℝ) • e from by
      rw [inner_add_left, he_inner, add_smul, one_smul]; abel]
    exact norm_perp_le_two_mul_norm he _

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [ProperSpace E] in
/-- Two vectors lying in the `r`-cap around `±e` lie in the `2r`-cap around each other. -/
private lemma min_norm_sub_add_le_two_mul {d₁ d₂ e : E} {r : ℝ}
    (h₁ : min ‖d₁ - e‖ ‖d₁ + e‖ ≤ r) (h₂ : min ‖d₂ - e‖ ‖d₂ + e‖ ≤ r) :
    min ‖d₁ - d₂‖ ‖d₁ + d₂‖ ≤ 2 * r := by
  have key : ∀ a b : E, ‖a‖ ≤ r → ‖b‖ ≤ r → ‖a - b‖ ≤ 2 * r ∧ ‖a + b‖ ≤ 2 * r := fun a b ha hb =>
    ⟨(norm_sub_le a b).trans (by linarith only [ha, hb]),
      (norm_add_le a b).trans (by linarith only [ha, hb])⟩
  rcases min_le_iff.mp h₁ with hb₁ | hb₁ <;> rcases min_le_iff.mp h₂ with hb₂ | hb₂
  · refine (min_le_left _ _).trans ?_
    have h := (key _ _ hb₁ hb₂).1
    rwa [sub_sub_sub_cancel_right] at h
  · refine (min_le_right _ _).trans ?_
    have h := (key _ _ hb₁ hb₂).2
    rwa [sub_add_add_cancel] at h
  · refine (min_le_right _ _).trans ?_
    have h := (key _ _ hb₁ hb₂).2
    rwa [add_add_sub_cancel] at h
  · refine (min_le_left _ _).trans ?_
    have h := (key _ _ hb₁ hb₂).1
    rwa [add_sub_add_right_eq_sub] at h

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E] in
/-- Replacing the unit vector `d` by the unit vector `e` in the orthogonal projection
`⟪v, ·⟫ • ·` costs at most `2‖v‖ · min ‖d ∓ e‖`. -/
private lemma norm_inner_smul_sub_inner_smul_le_min {v d e : E} (hd : ‖d‖ = 1) (he : ‖e‖ = 1) :
    ‖(inner ℝ v d : ℝ) • d - (inner ℝ v e : ℝ) • e‖ ≤ 2 * ‖v‖ * min ‖d - e‖ ‖d + e‖ := by
  have key : ∀ u : E, ‖u‖ = 1 →
      ‖(inner ℝ v u : ℝ) • u - (inner ℝ v e : ℝ) • e‖ ≤ 2 * ‖v‖ * ‖u - e‖ := by
    intro u hu
    have hin : (inner ℝ v (u - e) : ℝ) = inner ℝ v u - inner ℝ v e := by rw [inner_sub_right]
    have heq : (inner ℝ v u : ℝ) • u - (inner ℝ v e : ℝ) • e
        = (inner ℝ v u : ℝ) • (u - e) + (inner ℝ v (u - e) : ℝ) • e := by rw [hin]; module
    have h1 : |(inner ℝ v u : ℝ)| ≤ ‖v‖ := by simpa [hu] using abs_real_inner_le_norm v u
    have h2 : |(inner ℝ v (u - e) : ℝ)| ≤ ‖v‖ * ‖u - e‖ := abs_real_inner_le_norm _ _
    have h3 := mul_le_mul_of_nonneg_right h1 (norm_nonneg (u - e))
    rw [heq]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, he, mul_one]
    linarith only [h2, h3]
  rcases min_cases ‖d - e‖ ‖d + e‖ with ⟨hm, _⟩ | ⟨hm, _⟩
  · rw [hm]; exact key d hd
  · rw [hm]
    have h := key (-d) (by rw [norm_neg]; exact hd)
    rwa [show (inner ℝ v (-d) : ℝ) • (-d) = (inner ℝ v d : ℝ) • d from by
      rw [inner_neg_right]; module,
      show ‖-d - e‖ = ‖d + e‖ from by rw [show -d - e = -(d + e) from by abel, norm_neg]] at h

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E] in
/-- The `d`-coordinate of `v` differs from its `e`-coordinate by at most `‖v‖ · min ‖d ∓ e‖`. -/
private lemma abs_inner_le_abs_inner_add_mul_min {v d e : E} :
    |(inner ℝ v d : ℝ)| ≤ |(inner ℝ v e : ℝ)| + ‖v‖ * min ‖d - e‖ ‖d + e‖ := by
  have key : ∀ u : E, |(inner ℝ v u : ℝ)| ≤ ‖v‖ * ‖u‖ := fun u => abs_real_inner_le_norm v u
  rcases min_cases ‖d - e‖ ‖d + e‖ with ⟨hm, _⟩ | ⟨hm, _⟩
  · rw [hm, show (inner ℝ v d : ℝ) = inner ℝ v e + inner ℝ v (d - e) from by
      rw [inner_sub_right]; ring]
    exact (abs_add_le _ _).trans (by linarith only [key (d - e)])
  · rw [hm, show (inner ℝ v d : ℝ) = -inner ℝ v e + inner ℝ v (d + e) from by
      rw [inner_add_right]; ring]
    refine (abs_add_le _ _).trans ?_
    rw [abs_neg]
    linarith only [key (d + e)]

omit [MeasurableSpace E] [BorelSpace E] in
/-- A point of a tube's carrier splits the midpoint offset into an axial part of length at
most `1/2` and a transverse part of length at most `δ`. -/
private lemma exists_midpoint_sub_decomp {δ : NNReal} (t : Tube δ E) {p : E}
    (hp : p ∈ t.carrier) :
    ∃ (r : ℝ) (w : E), |r| ≤ 1 / 2 ∧ ‖w‖ ≤ (δ : ℝ) ∧
      t.midpoint - p = r • t.direction + w := by
  rw [t.carrier_eq] at hp
  obtain ⟨z, ⟨a, b, ha, hb, hab, hz⟩, hpz⟩ := Set.mem_iUnion₂.mp hp
  refine ⟨1 / 2 - b, z - p, by rw [abs_le]; constructor <;> linarith only [ha, hb, hab],
    by rw [← dist_eq_norm, dist_comm]; exact hpz, ?_⟩
  have hmz : t.midpoint - z = ((1 / 2 : ℝ) - b) • t.direction := by
    rw [← hz, show a = 1 - b from by linarith only [hab]]
    change (1 / 2 : ℝ) • (t.x + t.y) - ((1 - b) • t.x + b • t.y) = ((1 / 2 : ℝ) - b) • (t.y - t.x)
    module
  rw [← hmz]; abel

omit [MeasurableSpace E] [BorelSpace E] in
/-- Every point of a tube's carrier is within `1/2 + δ` of its midpoint. -/
private lemma norm_midpoint_sub_le {δ : NNReal} (t : Tube δ E) {p : E} (hp : p ∈ t.carrier) :
    ‖t.midpoint - p‖ ≤ 1 / 2 + (δ : ℝ) := by
  obtain ⟨r, w, hr, hw, hdec⟩ := exists_midpoint_sub_decomp t hp
  rw [hdec]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, Real.norm_eq_abs, t.norm_direction, mul_one]
  linarith only [hr, hw]

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Ball bound for `h_data` (perp-projection rescaled).**

For any `i ∈ s'` (i.e., a tube whose carrier contains `p`), the rescaled
perp-projection `g i = (1/δ) • ((T i).midpoint - ⟨(T i).midpoint, e⟩ • e)`
lies within `c_slide + 2` of `q = (1/δ) • (p - ⟨p, e⟩ • e)`.

Geometric content: since `p ∈ (T i).carrier`, there exists `z` on the
midpoint segment of `(T i)` with `dist p z ≤ δ`. The perp-projection of
`p - z` has norm `≤ δ`. The axial midpoint endpoint contributes at most
`1/2` to the perp deviation (rescaled axial-vs-tube-direction split via
`h_dir_class`), and the direction tilt `min ‖direction ∓ e‖ ≤ c_slide·δ`
contributes at most `(1/2) · c_slide · δ ≤ c_slide · δ`. Summing and
rescaling by `1/δ` yields `≤ 1 + c_slide + 1 = c_slide + 2`. -/
private lemma h_data_ball_bound_aux
    {c_slide : ℝ} (_hc_slide : 0 < c_slide)
    {δ : NNReal} (_hδ : 0 < δ)
    {ι : Type*} (s : Finset ι) (T : ι → Tube δ E)
    {e : E} (_he_unit : ‖e‖ = 1)
    (_h_dir_class : ∀ i ∈ s,
        min ‖(T i).direction - e‖ ‖(T i).direction + e‖ ≤ c_slide * (δ : ℝ))
    (p : E) :
    ∀ i ∈ (@Finset.filter ι (fun i => p ∈ (T i).carrier)
              (Classical.decPred _) s),
      ‖(1 / (δ : ℝ)) • ((T i).midpoint - inner ℝ (T i).midpoint e • e)
          - (1 / (δ : ℝ)) • (p - inner ℝ p e • e)‖ ≤ c_slide + 2 := by
  classical
  have hδr : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast _hδ
  intro i hi
  rw [Finset.mem_filter] at hi
  obtain ⟨r, w, hr, hw, hdec⟩ := exists_midpoint_sub_decomp (T i) hi.2
  have h_target_eq :
      (1 / (δ : ℝ)) • ((T i).midpoint - inner ℝ (T i).midpoint e • e)
        - (1 / (δ : ℝ)) • (p - inner ℝ p e • e)
        = (1 / (δ : ℝ)) • (r • ((T i).direction - inner ℝ (T i).direction e • e)
            + (w - inner ℝ w e • e)) := by
    rw [show r • ((T i).direction - (inner ℝ (T i).direction e : ℝ) • e)
          + (w - (inner ℝ w e : ℝ) • e)
        = (r • (T i).direction + w) - (inner ℝ (r • (T i).direction + w) e : ℝ) • e from by
      rw [inner_add_left, inner_smul_left, RCLike.conj_to_real]; module, ← hdec,
      inner_sub_left, sub_smul, smul_sub, smul_sub]
    module
  rw [h_target_eq, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0:ℝ) < 1 / (δ : ℝ))]
  have h1 : ‖r • ((T i).direction - (inner ℝ (T i).direction e : ℝ) • e)‖
      ≤ 1 / 2 * (2 * (c_slide * (δ : ℝ))) := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul hr ((norm_perp_le_two_mul_min _he_unit).trans
      (by linarith only [_h_dir_class i hi.1])) (norm_nonneg _) (by norm_num)
  have h2 : ‖w - (inner ℝ w e : ℝ) • e‖ ≤ 2 * (δ : ℝ) :=
    (norm_perp_le_two_mul_norm _he_unit w).trans (by linarith only [hw])
  calc (1 / (δ : ℝ)) * ‖r • ((T i).direction - (inner ℝ (T i).direction e : ℝ) • e)
          + (w - (inner ℝ w e : ℝ) • e)‖
      ≤ (1 / (δ : ℝ)) * (1 / 2 * (2 * (c_slide * (δ : ℝ))) + 2 * (δ : ℝ)) :=
        mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add h1 h2)) (by positivity)
    _ = c_slide + 2 := by field_simp

/-- **Pairwise separation for `h_data` (rescaled perp gap, sub-class
partition form).**

For distinct `i, j ∈ s' ∩ classify⁻¹{k}`, the rescaled perp-projections
satisfy `c_slide ≤ ‖g i - g j‖`. The classification `classify : ι → Fin K`
groups tubes by axial coordinate of their midpoint relative to `p` along
`e`, so that within a class the kappa-region hypothesis of
`ed_midpoint_perp_separation` is satisfied.

**Why a sub-class partition is needed.** The underlying
`ed_midpoint_perp_separation` requires the axial bound
`|inner (T_i.midpoint - T_j.midpoint) (T_j.direction)| ≤ 1/2 - κ`. Without
this, a parallel-offset counterexample exists (two tubes sharing direction
`e`, midpoints `±(1/2)·e`, both containing `p = 0`; weak ED holds but the
rescaled perp gap is zero). The partition by axial coordinate ensures that
within a class, axial differences are small, restoring the kappa-region.

The constants `c_slide, K, δ₀` are dimension-only. `δ₀ ≤ 1` is the
upper bound on `δ` inherited from `ed_midpoint_perp_separation`. -/
private lemma h_data_pairwise_sep_aux
    (_hn : 1 < Module.finrank ℝ E) :
    ∃ (c_slide : ℝ) (K : ℕ) (δ₀ : ℝ),
      0 < c_slide ∧ 0 < K ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {δ : NNReal} (_hδ : 0 < δ) (_hδ_le : (δ : ℝ) ≤ δ₀)
        {ι : Type*} (s : Finset ι) (T : ι → Tube δ E)
        (_hED : (s : Set ι).Pairwise
            (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier))
        {e : E} (_he_unit : ‖e‖ = 1)
        (_h_dir_class : ∀ i ∈ s,
            min ‖(T i).direction - e‖ ‖(T i).direction + e‖ ≤ c_slide * (δ : ℝ))
        (p : E),
        ∃ classify : ι → Fin K, ∀ k : Fin K,
          ((@Finset.filter ι
              (fun i => p ∈ (T i).carrier ∧ classify i = k)
              (Classical.decPred _) s : Finset ι) : Set ι).Pairwise
            (fun i j =>
              c_slide ≤
                ‖((1 / (δ : ℝ)) • ((T i).midpoint - inner ℝ (T i).midpoint e • e))
                  - ((1 / (δ : ℝ)) • ((T j).midpoint - inner ℝ (T j).midpoint e • e))‖) := by
  classical
  -- Get the underlying perp-midpoint separation constants.
  obtain ⟨c0, κ, δ₀, hc0_pos, hκ_pos, hκ_lt, hδ₀_pos, hδ₀_le, h_ed⟩ :=
    ed_midpoint_perp_separation (E := E) _hn
  have hκ' : 0 < 1 - 2 * κ := by linarith only [hκ_lt]
  -- Bin the axial coordinate into `Kn` bins of width `3/Kn ≤ (1 - 2κ)/4`, and shrink `δ₀`
  -- so that the direction-tilt slack `c0 · δ / 4` is also at most `(1 - 2κ)/4`.
  obtain ⟨Kn, hKn_pos, hKn_ge⟩ : ∃ Kn : ℕ, 0 < Kn ∧ 24 / (1 - 2 * κ) ≤ (Kn : ℝ) :=
    ⟨⌈(24 : ℝ) / (1 - 2 * κ)⌉₊ + 1, Nat.succ_pos _, by
      push_cast; linarith only [Nat.le_ceil ((24 : ℝ) / (1 - 2 * κ))]⟩
  obtain ⟨δ₁, hδ₁_pos, hδ₁_δ₀, hδ₁_half, hδ₁_κ⟩ :
      ∃ d : ℝ, 0 < d ∧ d ≤ δ₀ ∧ d ≤ 1 / 2 ∧ d ≤ (1 - 2 * κ) / c0 :=
    ⟨min δ₀ (min (1 / 2) ((1 - 2 * κ) / c0)),
      lt_min hδ₀_pos (lt_min (by norm_num) (by positivity)), min_le_left _ _,
      (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
  refine ⟨c0 / 8, Kn, δ₁, by positivity, hKn_pos, hδ₁_pos, by linarith only [hδ₁_half], ?_⟩
  intro δ hδ hδ_le ι s T hED e he_unit h_dir_class p
  have hδr : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  have hδ_half : (δ : ℝ) ≤ 1 / 2 := hδ_le.trans hδ₁_half
  have hKnR : (0 : ℝ) < (Kn : ℝ) := by exact_mod_cast hKn_pos
  -- The rescaled axial coordinate `f t ∈ [Kn/6, 5Kn/6] ⊆ [0, Kn)`; its floor is the bin.
  set f : ι → ℝ := fun t => ((inner ℝ ((T t).midpoint - p) e : ℝ) + 3 / 2) * ((Kn : ℝ) / 3)
    with hf_def
  have hf_mem : ∀ t : ι, p ∈ (T t).carrier → 0 ≤ f t ∧ f t < (Kn : ℝ) := by
    intro t ht
    have hax : |(inner ℝ ((T t).midpoint - p) e : ℝ)| ≤ 1 := by
      have h := abs_real_inner_le_norm ((T t).midpoint - p) e
      rw [he_unit, mul_one] at h
      linarith only [h, hδ_half, norm_midpoint_sub_le (T t) ht]
    rw [abs_le] at hax
    have hK3 : (0 : ℝ) < (Kn : ℝ) / 3 := by positivity
    refine ⟨mul_nonneg (by linarith only [hax.1]) hK3.le, ?_⟩
    simp only [hf_def]
    linarith only [mul_lt_mul_of_pos_right
      (show (inner ℝ ((T t).midpoint - p) e : ℝ) + 3 / 2 < 3 by linarith only [hax.2]) hK3]
  refine ⟨fun t => ⟨⌊f t⌋.toNat % Kn, Nat.mod_lt _ hKn_pos⟩, ?_⟩
  intro k i hi j hj hij
  -- Unpack membership.
  simp only [Finset.coe_filter, Set.mem_setOf_eq] at hi hj
  obtain ⟨hi_s, hi_p, hi_class⟩ := hi
  obtain ⟨hj_s, hj_p, hj_class⟩ := hj
  -- Being in the same bin forces equal floors, hence a small axial gap.
  have hmod : ∀ t : ι, p ∈ (T t).carrier → ⌊f t⌋.toNat % Kn = ⌊f t⌋.toNat := fun t ht =>
    Nat.mod_eq_of_lt (by
      rw [Int.toNat_lt' (by omega)]
      exact_mod_cast Int.floor_lt.mpr (by exact_mod_cast (hf_mem t ht).2))
  have h_floor_eq : ⌊f i⌋ = ⌊f j⌋ := by
    have h : ⌊f i⌋.toNat % Kn = ⌊f j⌋.toNat % Kn :=
      congrArg Fin.val (hi_class.trans hj_class.symm)
    rw [hmod i hi_p, hmod j hj_p] at h
    have h0i : 0 ≤ ⌊f i⌋ := Int.floor_nonneg.mpr (hf_mem i hi_p).1
    have h0j : 0 ≤ ⌊f j⌋ := Int.floor_nonneg.mpr (hf_mem j hj_p).1
    omega
  obtain ⟨v, hv⟩ : ∃ v : E, (T i).midpoint - (T j).midpoint = v := ⟨_, rfl⟩
  have h_axial : |(inner ℝ v e : ℝ)| ≤ (1 - 2 * κ) / 4 := by
    have h1 : |f i - f j| < 1 := by
      have hi1 := Int.floor_le (f i)
      have hi2 := Int.lt_floor_add_one (f i)
      rw [h_floor_eq] at hi1 hi2
      rw [abs_sub_lt_iff]
      constructor <;>
        linarith only [hi1, hi2, Int.floor_le (f j), Int.lt_floor_add_one (f j)]
    rw [show f i - f j = (inner ℝ v e : ℝ) * ((Kn : ℝ) / 3) from by
        simp only [hf_def, ← hv, inner_sub_left]; ring,
      abs_mul, abs_of_pos (show (0 : ℝ) < (Kn : ℝ) / 3 by positivity)] at h1
    have h3 : 3 / (Kn : ℝ) ≤ (1 - 2 * κ) / 4 := by
      rw [div_le_div_iff₀ hKnR (by norm_num : (0 : ℝ) < 4)]
      rw [div_le_iff₀ hκ'] at hKn_ge
      linarith only [hKn_ge]
    linarith only [h3, (lt_div_iff₀ hKnR).mpr
      (show |(inner ℝ v e : ℝ)| * (Kn : ℝ) < 3 by linarith only [h1])]
  have hv_norm : ‖v‖ ≤ 2 := by
    rw [← hv, show (T i).midpoint - (T j).midpoint
        = ((T i).midpoint - p) - ((T j).midpoint - p) from by abel]
    exact (norm_sub_le _ _).trans (by
      linarith only [hδ_half, norm_midpoint_sub_le (T i) hi_p, norm_midpoint_sub_le (T j) hj_p])
  have h_dir_j := h_dir_class j hj_s
  have hc0δ : c0 * (δ : ℝ) ≤ 1 - 2 * κ := by
    linarith only [(le_div_iff₀ hc0_pos).mp (hδ_le.trans hδ₁_κ)]
  -- The axial coordinate along `(T j).direction` stays inside the kappa-region.
  have h_vdj : |(inner ℝ v (T j).direction : ℝ)| ≤ 1 / 2 - κ := by
    have h1 : ‖v‖ * min ‖(T j).direction - e‖ ‖(T j).direction + e‖ ≤ 2 * (c0 / 8 * (δ : ℝ)) :=
      mul_le_mul hv_norm h_dir_j (le_min (norm_nonneg _) (norm_nonneg _)) (by norm_num)
    linarith only [h1, h_axial, hc0δ,
      abs_inner_le_abs_inner_add_mul_min (v := v) (d := (T j).direction) (e := e)]
  -- Apply `ed_midpoint_perp_separation` in the direction of `T j`.
  have h_perp_dj : c0 * (δ : ℝ) < ‖v - (inner ℝ v (T j).direction : ℝ) • (T j).direction‖ := by
    have h := h_ed hδ (hδ_le.trans hδ₁_δ₀) (T i) (T j) (hED hi_s hj_s hij)
      ((min_norm_sub_add_le_two_mul (h_dir_class i hi_s) h_dir_j).trans
        (by linarith only [mul_nonneg hc0_pos.le hδr.le])) (by rw [hv]; exact h_vdj)
    rwa [hv] at h
  -- Swapping `(T j).direction` for `e` in the projection costs at most `c0 δ / 2`.
  have h_perp_e : c0 / 8 * (δ : ℝ) < ‖v - (inner ℝ v e : ℝ) • e‖ := by
    have hbr : ‖(inner ℝ v (T j).direction : ℝ) • (T j).direction - (inner ℝ v e : ℝ) • e‖
        ≤ 2 * ‖v‖ * (c0 / 8 * (δ : ℝ)) :=
      (norm_inner_smul_sub_inner_smul_le_min (T j).norm_direction he_unit).trans
        (mul_le_mul_of_nonneg_left h_dir_j (by positivity))
    have hkey : ‖v - (inner ℝ v (T j).direction : ℝ) • (T j).direction‖
        - ‖v - (inner ℝ v e : ℝ) • e‖ ≤ 2 * ‖v‖ * (c0 / 8 * (δ : ℝ)) := by
      refine (norm_sub_norm_le _ _).trans ?_
      rwa [show v - (inner ℝ v (T j).direction : ℝ) • (T j).direction
            - (v - (inner ℝ v e : ℝ) • e)
          = -((inner ℝ v (T j).direction : ℝ) • (T j).direction - (inner ℝ v e : ℝ) • e) from by
        abel, norm_neg]
    have hb : 2 * ‖v‖ * (c0 / 8 * (δ : ℝ)) ≤ c0 * (δ : ℝ) / 2 := by
      linarith only [mul_nonneg (sub_nonneg.mpr hv_norm) (mul_pos hc0_pos hδr).le]
    linarith only [hkey, hb, h_perp_dj, mul_pos hc0_pos hδr]
  -- Rescale by `1/δ`.
  rw [show (1 / (δ : ℝ)) • ((T i).midpoint - (inner ℝ (T i).midpoint e : ℝ) • e)
        - (1 / (δ : ℝ)) • ((T j).midpoint - (inner ℝ (T j).midpoint e : ℝ) • e)
      = (1 / (δ : ℝ)) • (v - (inner ℝ v e : ℝ) • e) from by rw [← hv, inner_sub_left]; module,
    norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 1 / (δ : ℝ)), one_div,
    inv_mul_eq_div, le_div_iff₀ hδr]
  linarith only [h_perp_e]

/-- **Multiplicity-at-a-point sub-lemma (technical heart).**

Encapsulates the geometric content of
`multiplicity_le_of_ED_directionClass`: the perp-projection
`c_slide·δ`-separation forced by ED (`ed_midpoint_perp_separation`),
the boundedness of feasible projected midpoints (in a fixed-radius
ball through `p`), and the `n`-dimensional packing estimate after
rescaling by `1/δ`. The witness `C` is dimension-only (depends on
`finrank ℝ E` and `c_slide`).

The proof reduces to two genuinely smaller pieces: the abstract
packing bound `packing_bound_aux`, and the tube-to-packing-data
conversion captured by `h_data_ball_bound_aux` and
`h_data_pairwise_sep_aux`. -/
private lemma multiplicity_at_point_aux
    (_hn : 1 < Module.finrank ℝ E) :
    ∃ (c_slide : ℝ) (C : ℕ) (δ₀ : ℝ),
      0 < c_slide ∧ 0 < C ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {δ : NNReal} (_hδ : 0 < δ) (_hδ_le : (δ : ℝ) ≤ δ₀)
        {ι : Type*} (s : Finset ι) (T : ι → Tube δ E)
        (_hED : (s : Set ι).Pairwise
            (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier))
        {e : E} (_he_unit : ‖e‖ = 1)
        (_h_dir_class : ∀ i ∈ s,
            min ‖(T i).direction - e‖ ‖(T i).direction + e‖ ≤ c_slide * (δ : ℝ))
        (p : E),
        ((@Finset.filter ι (fun i => p ∈ (T i).carrier)
            (Classical.decPred _) s).card) ≤ C := by
  classical
  obtain ⟨c_slide, K, δ₀, hc_slide_pos, hK_pos, hδ₀_pos, hδ₀_le, h_sep_data⟩ :=
    h_data_pairwise_sep_aux (E := E) _hn
  obtain ⟨N, hN_pos, hN_bnd⟩ :=
    packing_bound_aux (Module.finrank ℝ E) (c_slide + 2) c_slide
      (by linarith only [hc_slide_pos]) hc_slide_pos
  -- Witness: `C := K * N` covers the `δ ≤ δ₀` regime, which is now the only regime.
  refine ⟨c_slide, K * N, δ₀, hc_slide_pos, Nat.mul_pos hK_pos hN_pos, hδ₀_pos, hδ₀_le, ?_⟩
  intro δ hδ hδ_le ι s T hED e he_unit h_dir_class p
  set s' : Finset ι :=
    (@Finset.filter ι (fun i => p ∈ (T i).carrier) (Classical.decPred _) s) with hs'_def
  obtain ⟨classify, h_sep_k⟩ := h_sep_data hδ hδ_le s T hED he_unit h_dir_class p
  -- Each fiber `s'.filter (classify · = k)` has card ≤ N by packing.
  have h_card_k : ∀ k : Fin K, (s'.filter fun i => classify i = k).card ≤ N := fun k =>
    hN_bnd (F := E) rfl _
      (fun i => (1 / (δ : ℝ)) • ((T i).midpoint - inner ℝ (T i).midpoint e • e))
      ((1 / (δ : ℝ)) • (p - inner ℝ p e • e))
      (fun i hi => h_data_ball_bound_aux hc_slide_pos hδ s T he_unit h_dir_class p i
        (Finset.mem_filter.mp hi).1)
      (by
        -- Bridge the lemma's filter shape `{i ∈ s | p ∈ T i ∧ classify i = k}` to ours.
        rw [show (s'.filter fun i => classify i = k)
              = @Finset.filter ι (fun i => p ∈ (T i).carrier ∧ classify i = k)
                  (Classical.decPred _) s from by
                rw [hs'_def]; ext i; simp only [Finset.mem_filter, and_assoc]]
        exact h_sep_k k)
  -- Combine via `card_eq_sum_card_fiberwise`: `s'` is the disjoint union of the fibers.
  rw [Finset.card_eq_sum_card_fiberwise (f := classify) (s := s')
    (t := (Finset.univ : Finset (Fin K))) fun i _ => Finset.mem_univ _]
  calc (∑ k : Fin K, (s'.filter fun i => classify i = k).card)
      ≤ ∑ _k : Fin K, N := Finset.sum_le_sum fun k _ => h_card_k k
    _ = K * N := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- **Pointwise multiplicity bound: through any point, the number of
pairwise-ED δ-tubes whose directions lie in a common `c_slide·δ`-cap
is at most `C_n`.**

By `ed_midpoint_perp_separation`, the perp-projected midpoints of such
tubes form a `c_slide·δ`-separated set in the (n-1)-dimensional
orthogonal hyperplane. The standard `(n-1)`-dim packing bound (within
the radius `2`-ball of feasible midpoints) gives at most `C_n` such
tubes through any single point.

The `∃ C` is pulled outside the universal binders over `δ, ι, s, T,
e, p`, so any witness must work uniformly in those data. `C` is
allowed to depend on the cap-radius constant `c_slide` and on `E`
(via finrank).

Reduces to the sub-lemma `multiplicity_at_point_aux`, which
encapsulates the full geometric content. This is the multiplicity
bound used in the volume double-counting step. -/
lemma multiplicity_le_of_ED_directionClass
    (_hn : 1 < Module.finrank ℝ E) :
    ∃ (c_slide : ℝ) (C : ℕ) (δ₀ : ℝ),
      0 < c_slide ∧ 0 < C ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {δ : NNReal} (_hδ : 0 < δ) (_hδ_le : (δ : ℝ) ≤ δ₀)
        {ι : Type*} (s : Finset ι) (T : ι → Tube δ E)
        (_hED : (s : Set ι).Pairwise
            (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier))
        {e : E} (_he_unit : ‖e‖ = 1)
        (_h_dir_class : ∀ i ∈ s,
            min ‖(T i).direction - e‖ ‖(T i).direction + e‖ ≤ c_slide * (δ : ℝ))
        (p : E),
        ((@Finset.filter ι (fun i => p ∈ (T i).carrier)
            (Classical.decPred _) s).card) ≤ C :=
  multiplicity_at_point_aux _hn

end -- close noncomputable section
end Kakeya

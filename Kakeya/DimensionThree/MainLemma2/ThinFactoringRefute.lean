/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.ThinProduceParts
public import Mathlib.Analysis.PSeries

/-!
# `Kakeya.ThinCase.factoringApply` is false as stated, and the exact missing hypothesis

This file proves
that it cannot be proved: two of its thirteen conclusions,

* **(iv)** the centred multiplicity comparison at *equal* radii,
  `|U(𝕋', Y') ∩ B(x, w₁)| ≤ C |U(𝕋', Y') ∩ B(y, w₁)|` for all `x, y` in the outer shaded union,
* **(vi)** the summed refinement `C⁻¹ ∑_{p ∈ 𝕋} |Y(p)| ≤ ∑_{p ∈ 𝕋'} |Y'(p)|`,

are jointly unachievable with the constant `Kakeya.ThinCase.factoringApplyConstant CF Cfull
Ccore`, whose only inputs are `CF`, `Cfull` and — through `Ccore` — `segs.card`, `bodies.card`
and `δ`.

## What the refutation is

`Kakeya.ThinCase.Refute.factoringApply_refuted` derives `False` from
`Kakeya.ThinCase.Refute.FactoringApplyStatement`, the statement of `factoringApply` with all
binders made explicit and **without the localisation hypothesis**.

`factoringApply` now carries that hypothesis,
`hloc : ∃ z : E, ∀ j ∈ bodies, (Wb j).carrier ⊆ Metric.closedBall z 1`, and
`Kakeya.ThinCase.Refute.statement_of_universal_loc` is the tripwire in its repaired form: it
derives `FactoringApplyStatement` from the current declaration by granting `hloc` for free and
passing every other argument through verbatim, so it typechecks exactly as long as `hloc` is
the only *ungranted* difference. The hypothesis is discharged at the sole call site
(`Kakeya.ThinCase.perBall` → `Kakeya.ThinCase.thinSetupExists` →
`Kakeya.VeryNotSticky.exists_thinConfig`, from
`Kakeya.VeryNotSticky.BallData.bodies_subset_ball` and `r₁ = δ^exscal ≤ 1`).

`factoringApply` also carries the *second* field of
`ShadedBody.FactorFamily.InnerIsDiscretizedAtScale` — a discretization scale `δ₀` with
`hscale : ∀ p ∈ segs, δ₀ ≤ ethickness.scale ℝ (Y p).carrier`, together with the two
scale-dependent envelope bounds at `δ₀`. Those are *not* granted by the tripwire: they are part
of `FactoringApplyStatement` and the counterexample supplies them, at `δ₀ = δ = 1 / 2`, via
`Kakeya.ThinCase.Refute.scale_capsule_ge`. So the refutation is strictly stronger than the one
first recorded: the statement is false even with the discretization hypothesis in hand at the
full scale `δ`, `subset_unitBall` being the missing field.

The witness uses **one** segment inside **one** body, so that neither `segs.card` nor
`bodies.card` can grow with the configuration, and `C := factoringApplyConstant 1 1
(factoringApplyCore 3 1 1 (1/2))` is one fixed number:

* the body is `Kakeya.ThinCase.Refute.capsule M`, the closed `1/2`-neighbourhood of the segment
  from `0` to `2 (M+1)` on the first coordinate axis of `EuclideanSpace ℝ (Fin 3)`. Its
  `2`-thickness is exactly `1/2` (`thickness_capsule_le`, `thickness_capsule_ge`), so the width
  hypothesis `hw₁` holds at `w₁ = 1`;
* the shading is `Kakeya.ThinCase.Refute.shadeSet M = ⋃_{k < M} blob k`, where `blob k` is the
  closed ball of radius `(1/4) (k+1)^(-1/3)` about `2 (k+1)` on the axis. The blobs are
  pairwise `2`-separated, so `B(x, 1)` meets exactly the blob containing `x`
  (`inter_ball_eq`), and `(k+1) |blob k| = massUnit` is constant
  (`succ_mul_volume_blob`): the mass profile is harmonic;
* `δ = 1/2`, `w₁ = 1`, `CF = Cfull = 1`, `Ccore = factoringApplyCore 3 1 1 (1/2)`, and `η` is a
  natural number large enough for the fullness hypothesis (`exists_eta`). One segment in its own
  body is `1`-Frostman (`isFrostmanIn_self`), so `hFr` holds with `CF = 1`.

`Kakeya.ThinCase.Refute.harmonic_le_of_centredMult` is the counting core. Clause (iv) forces the
retained blob masses to be pairwise comparable up to `C`; because `(k+1) |blob k|` is constant,
comparability caps the *number* of surviving blobs, and the retained mass at `C * massUnit`.
Clause (vi) demands at least `C⁻¹ * massUnit * H_M`. Hence `H_M ≤ C ^ 2` for every `M`, and the
harmonic series diverges.

## What the missing hypothesis is

`Kakeya.ThinCase.Refute.not_subset_closedBall_one`: the refuting body has diameter `2 M`, so it
violates `ConvexSpaceBody.IsDiscretizedAtScale.subset_unitBall`, the first field of
`ShadedBody.FactorFamily.InnerIsDiscretizedAtScale δ` — a hypothesis of *every* item of GWZ
Proposition 5.1 in this repository, item 7
(`ShadedBody.outerFactoringFamily_avgMultOnBalls`) included, and one that `factoringApply`
does not carry. Under it, and with `δ ≤ w₁`, the shaded union is covered by at most
`(1 + 4/δ) ^ n` balls of radius `w₁ / 2`, so the Step 5 dyadic mass pigeonhole
(`Kakeya.factoringStep5SelfPigeonholeConstant`) costs `O(n log δ⁻¹)` — subpolynomial in `δ⁻¹`,
hence inside the `Ccore` budget. Without it the covering number is unbounded and no
cardinality-only constant can pay for it.

## The positive half

`Kakeya.ThinCase.Localise.exists_localised_refinement` and
`exists_localised_refinement_of_subset_ball` price clause (iv) exactly: keeping the heaviest
half-ball of a `w₁/2`-net gives clause (iv) with constant `1`, at a mass cost equal to the
covering number of the shaded union at scale `w₁ / 2`, which is `≤ (1 + 4 R / w₁) ^ n` when the
union sits in a ball of radius `R`. (The sharp cost is the logarithm of that number, via the
dyadic mass pigeonhole that Step 5 already performs; the crude bound above is what is needed to
see *which* quantity the constant must depend on.)

Nothing in this file changes any existing statement, and nothing in the repository depends on
it.
-/

@[expose] public section

namespace Kakeya.ThinCase.Refute

open MeasureTheory Metric Set ShadedBody Filter

/-- The ambient space of the counterexample. -/
abbrev E3 : Type := EuclideanSpace ℝ (Fin 3)

/-- The centre of the `k`-th blob: the point `2 (k+1)` on the first coordinate axis. -/
noncomputable def ctr (k : ℕ) : E3 := EuclideanSpace.single (0 : Fin 3) (2 * ((k : ℝ) + 1))

/-- The radius of the `k`-th blob. -/
noncomputable def rad (k : ℕ) : ℝ := (1 / 4 : ℝ) * ((k : ℝ) + 1) ^ (-(1 : ℝ) / 3)

/-- The `k`-th blob. -/
noncomputable def blob (k : ℕ) : Set E3 := Metric.closedBall (ctr k) (rad k)

/-- The shading of the counterexample: the union of the first `M` blobs. -/
noncomputable def shadeSet (M : ℕ) : Set E3 := ⋃ k ∈ Finset.range M, blob k

lemma one_le_succ (k : ℕ) : (1 : ℝ) ≤ (k : ℝ) + 1 := by
  have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  linarith

lemma rad_pos (k : ℕ) : 0 < rad k := by
  have h : (0 : ℝ) < ((k : ℝ) + 1) := by positivity
  have := Real.rpow_pos_of_pos h (-(1 : ℝ) / 3)
  unfold rad; positivity

lemma rad_le (k : ℕ) : rad k ≤ 1 / 4 := by
  have h1 : (1 : ℝ) ≤ ((k : ℝ) + 1) := by
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have := Real.rpow_le_one_of_one_le_of_nonpos h1 (by norm_num : (-(1:ℝ)/3) ≤ 0)
  unfold rad; nlinarith [this]

lemma rad_cube (k : ℕ) : rad k ^ 3 = (1 / 64 : ℝ) / ((k : ℝ) + 1) := by
  have h : (0 : ℝ) < ((k : ℝ) + 1) := by positivity
  unfold rad
  rw [mul_pow]
  rw [← Real.rpow_natCast (((k : ℝ) + 1) ^ (-(1 : ℝ) / 3)) 3, ← Real.rpow_mul h.le]
  norm_num
  rw [Real.rpow_neg_one]
  ring

/-! ### Separation and locality -/

lemma dist_ctr (k l : ℕ) : dist (ctr k) (ctr l) = |2 * ((k : ℝ) + 1) - 2 * ((l : ℝ) + 1)| := by
  unfold ctr
  rw [show dist (EuclideanSpace.single (0 : Fin 3) (2 * ((k : ℝ) + 1)))
        (EuclideanSpace.single (0 : Fin 3) (2 * ((l : ℝ) + 1)))
      = dist (2 * ((k : ℝ) + 1)) (2 * ((l : ℝ) + 1)) from
    PiLp.dist_single_same 2 (fun _ => ℝ) _ _ _]
  exact Real.dist_eq _ _

lemma two_le_dist_ctr {k l : ℕ} (h : k ≠ l) : 2 ≤ dist (ctr k) (ctr l) := by
  rw [dist_ctr]
  have hne : (k : ℝ) ≠ (l : ℝ) := by exact_mod_cast h
  have h1 : (1 : ℝ) ≤ |(k : ℝ) - (l : ℝ)| := by
    rcases lt_or_gt_of_ne h with hlt | hgt
    · have : (k : ℕ) + 1 ≤ l := hlt
      have : ((k : ℝ)) + 1 ≤ (l : ℝ) := by exact_mod_cast this
      rw [abs_of_nonpos (by linarith)]; linarith
    · have : (l : ℕ) + 1 ≤ k := hgt
      have : ((l : ℝ)) + 1 ≤ (k : ℝ) := by exact_mod_cast this
      rw [abs_of_nonneg (by linarith)]; linarith
  have : |2 * ((k : ℝ) + 1) - 2 * ((l : ℝ) + 1)| = 2 * |(k : ℝ) - (l : ℝ)| := by
    rw [show 2 * ((k : ℝ) + 1) - 2 * ((l : ℝ) + 1) = 2 * ((k : ℝ) - (l : ℝ)) by ring,
      abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  rw [this]; linarith

lemma dist_le_of_mem_blob {k : ℕ} {z : E3} (hz : z ∈ blob k) : dist z (ctr k) ≤ 1 / 4 :=
  le_trans (Metric.mem_closedBall.mp hz) (rad_le k)

/-- Locality: a point of `blob l` within distance `1` of a point of `blob k` forces `k = l`. -/
lemma blob_eq_of_close {k l : ℕ} {x z : E3} (hx : x ∈ blob k) (hz : z ∈ blob l)
    (hxz : dist z x < 1) : k = l := by
  by_contra hne
  have h2 : (2 : ℝ) ≤ dist (ctr k) (ctr l) := two_le_dist_ctr hne
  have hk := dist_le_of_mem_blob hx
  have hl := dist_le_of_mem_blob hz
  have : dist (ctr k) (ctr l) ≤ dist (ctr k) x + dist x z + dist z (ctr l) :=
    le_trans (dist_triangle (ctr k) z (ctr l)) (by
      have := dist_triangle (ctr k) x z; linarith)
  rw [dist_comm (ctr k) x, dist_comm x z] at this
  linarith

/-- A blob is contained in the unit ball around any of its points. -/
lemma blob_subset_ball {k : ℕ} {x : E3} (hx : x ∈ blob k) : blob k ⊆ Metric.ball x 1 := by
  intro z hz
  have hk := dist_le_of_mem_blob hx
  have hl := dist_le_of_mem_blob hz
  have : dist z x ≤ dist z (ctr k) + dist (ctr k) x := dist_triangle _ _ _
  rw [dist_comm (ctr k) x] at this
  exact Metric.mem_ball.mpr (by linarith)

lemma blob_disjoint {k l : ℕ} (h : k ≠ l) : Disjoint (blob k) (blob l) := by
  rw [Set.disjoint_left]
  intro z hzk hzl
  exact h (blob_eq_of_close hzk hzl (by simp))

lemma measurableSet_blob (k : ℕ) : MeasurableSet (blob k) := measurableSet_closedBall

/-! ### Volumes -/

/-- The volume of the unit ball, the normalising constant of the configuration. -/
noncomputable def v0 : ENNReal := volume (Metric.ball (0 : E3) 1)

lemma v0_pos : 0 < v0 := measure_ball_pos _ _ one_pos

lemma v0_ne_top : v0 ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (measure_mono Metric.ball_subset_closedBall)
  exact (isCompact_closedBall (0 : E3) 1).measure_lt_top.ne

lemma volume_blob (k : ℕ) :
    volume (blob k) = ENNReal.ofReal ((1 / 64 : ℝ) / ((k : ℝ) + 1)) * v0 := by
  unfold blob v0
  rw [Measure.addHaar_closedBall volume (ctr k) (rad_pos k).le]
  congr 2
  rw [show Module.finrank ℝ E3 = 3 from finrank_euclideanSpace_fin]
  exact rad_cube k

/-! ### The carrier: a capsule of thickness `1/2` around the first coordinate axis -/

/-- The unit vector along the first coordinate axis. -/
noncomputable def axisVec : E3 := EuclideanSpace.single (0 : Fin 3) (1 : ℝ)

lemma ctr_eq_smul (k : ℕ) : ctr k = (2 * ((k : ℝ) + 1)) • axisVec := by
  unfold ctr axisVec
  ext i
  simp

lemma smul_ctr {k M : ℕ} :
    (((k : ℝ) + 1) / ((M : ℝ) + 1)) • ctr M = ctr k := by
  have hM : ((M : ℝ) + 1) ≠ 0 := by positivity
  rw [ctr_eq_smul, ctr_eq_smul, smul_smul]
  congr 1
  field_simp

/-- The spine of the capsule: the segment from the origin to the last centre. -/
noncomputable def spine (M : ℕ) : Set E3 := segment ℝ (0 : E3) (ctr M)

lemma ctr_mem_spine {k M : ℕ} (h : k ≤ M) : ctr k ∈ spine M := by
  have hM : (0 : ℝ) < ((M : ℝ) + 1) := by positivity
  have hkM : ((k : ℝ) + 1) ≤ ((M : ℝ) + 1) := by
    have : (k : ℝ) ≤ (M : ℝ) := by exact_mod_cast h
    linarith
  refine ⟨1 - ((k : ℝ) + 1) / ((M : ℝ) + 1), ((k : ℝ) + 1) / ((M : ℝ) + 1), ?_, ?_, by ring, ?_⟩
  · have : ((k : ℝ) + 1) / ((M : ℝ) + 1) ≤ 1 := by
      rw [div_le_one hM]; exact hkM
    linarith
  · positivity
  · rw [smul_zero, zero_add, smul_ctr]

/-- The carrier of the counterexample: the closed `1/2`-neighbourhood of the spine. -/
noncomputable def capsule (M : ℕ) : Set E3 := Metric.cthickening (1 / 2) (spine M)

lemma isCompact_capsule (M : ℕ) : IsCompact (capsule M) :=
  isCompact_segment.cthickening

lemma convex_capsule (M : ℕ) : Convex ℝ (capsule M) :=
  (convex_segment _ _).cthickening _

lemma capsule_nonempty (M : ℕ) : (capsule M).Nonempty :=
  ⟨0, Metric.self_subset_cthickening _ (left_mem_segment _ _ _)⟩

lemma blob_subset_capsule {k M : ℕ} (h : k < M) : blob k ⊆ capsule M := by
  intro z hz
  refine Metric.mem_cthickening_of_dist_le z (ctr k) (1 / 2) _
    (ctr_mem_spine h.le) ?_
  linarith [dist_le_of_mem_blob hz]

lemma shadeSet_subset_capsule (M : ℕ) : shadeSet M ⊆ capsule M := by
  intro z hz
  obtain ⟨k, hk, hzk⟩ := Set.mem_iUnion₂.mp hz
  exact blob_subset_capsule (Finset.mem_range.mp hk) hzk

lemma closedBall_subset_capsule (M : ℕ) : Metric.closedBall (0 : E3) (1 / 2) ⊆ capsule M :=
  Metric.closedBall_subset_cthickening (left_mem_segment _ _ _) _

/-- The capsule has `2`-thickness exactly `1/2`: it lies in the `1/2`-neighbourhood of a line,
and it contains a ball of radius `1/2`. -/
lemma thickness_capsule_le (M : ℕ) : Metric.thickness ℝ (capsule M) 2 ≤ 1 / 2 := by
  set R := { ε : ℝ | 0 ≤ ε ∧ ∃ A : AffineSubspace ℝ E3,
    Module.rank ℝ A.direction ≤ 2 ∧ capsule M ⊆ Metric.cthickening ε A } with hR
  have hbdd : BddBelow R := ⟨0, fun _ ↦ And.left⟩
  refine csInf_le hbdd ⟨by norm_num, ?_⟩
  refine ⟨(Submodule.span ℝ {axisVec}).toAffineSubspace, ?_, ?_⟩
  · rw [Submodule.toAffineSubspace_direction]
    refine le_trans (rank_span_le _) ?_
    rw [Cardinal.mk_singleton]
    norm_num
  · refine cthickening_subset_of_subset _ ?_
    have hsub : spine M ⊆ ((Submodule.span ℝ {axisVec}).toAffineSubspace : Set E3) := by
      have h0 : (0 : E3) ∈ ((Submodule.span ℝ {axisVec}).toAffineSubspace : Set E3) :=
        Submodule.zero_mem _
      have h1 : ctr M ∈ ((Submodule.span ℝ {axisVec}).toAffineSubspace : Set E3) := by
        change ctr M ∈ Submodule.span ℝ {axisVec}
        rw [ctr_eq_smul]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
      exact (Submodule.span ℝ {axisVec}).convex.segment_subset h0 h1
    exact hsub

lemma thickness_capsule_ge (M : ℕ) : (1 : ℝ) / 2 ≤ Metric.thickness ℝ (capsule M) 2 := by
  have h1 : Metric.thickness ℝ (Metric.closedBall (0 : E3) (1 / 2)) 2 ≤
      Metric.thickness ℝ (capsule M) 2 :=
    Metric.thickness_monotone (isCompact_capsule M).isBounded (closedBall_subset_capsule M) 2
  refine le_trans ?_ h1
  refine Metric.thickness_closedBall_ge (by norm_num) ?_
  rw [show Module.finrank ℝ E3 = 3 from finrank_euclideanSpace_fin]
  norm_num

/-! ### The mass profile -/

/-- The common mass unit of the configuration: `(k+1) * |blob k|` for every `k`. -/
noncomputable def massUnit : ENNReal := ENNReal.ofReal (1 / 64 : ℝ) * v0

lemma massUnit_pos : 0 < massUnit := by
  refine ENNReal.mul_pos ?_ v0_pos.ne'
  simp

lemma massUnit_ne_top : massUnit ≠ ⊤ :=
  ENNReal.mul_ne_top ENNReal.ofReal_ne_top v0_ne_top

lemma succ_mul_volume_blob (k : ℕ) :
    ((k : ENNReal) + 1) * volume (blob k) = massUnit := by
  have hk : (0 : ℝ) < ((k : ℝ) + 1) := by positivity
  rw [volume_blob, massUnit, ← mul_assoc]
  congr 1
  rw [show ((k : ENNReal) + 1) = ENNReal.ofReal ((k : ℝ) + 1) by
    rw [ENNReal.ofReal_add (by positivity) zero_le_one]; simp,
    ← ENNReal.ofReal_mul hk.le]
  congr 1
  field_simp

lemma volume_blob_le (k : ℕ) : volume (blob k) ≤ massUnit := by
  refine le_trans ?_ (le_of_eq (succ_mul_volume_blob k))
  exact le_mul_of_one_le_left' (by simp)

lemma volume_shadeSet (M : ℕ) :
    volume (shadeSet M) = ENNReal.ofReal ((1 / 64 : ℝ) * ∑ k ∈ Finset.range M, 1 / ((k : ℝ) + 1))
      * v0 := by
  unfold shadeSet
  rw [measure_biUnion_finset (fun k _ l _ hkl => blob_disjoint hkl)
    (fun k _ => measurableSet_blob k)]
  rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg (fun k _ => by positivity), Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [volume_blob]
  congr 2
  ring

/-! ### Locality -/

lemma inter_ball_eq {M k : ℕ} {U' : Set E3} (hsub : U' ⊆ shadeSet M) {x : E3}
    (hx : x ∈ blob k) : U' ∩ Metric.ball x 1 = U' ∩ blob k := by
  apply Set.Subset.antisymm
  · rintro z ⟨hzU, hzb⟩
    obtain ⟨l, hl, hzl⟩ := Set.mem_iUnion₂.mp (hsub hzU)
    have : k = l := blob_eq_of_close hx hzl (Metric.mem_ball.mp hzb)
    exact ⟨hzU, this ▸ hzl⟩
  · rintro z ⟨hzU, hzb⟩
    exact ⟨hzU, blob_subset_ball hx hzb⟩

/-! ### The counting core -/

/-- **The counting core of the refutation.**

If a measurable subset `U'` of the harmonic configuration `shadeSet M` satisfies the
equal-radius centred multiplicity bound of clause (iv) of `Kakeya.ThinCase.factoringApply` with
constant `C`, and retains at least a `C⁻¹` fraction of the mass as clause (vi) demands, then the
`M`-th harmonic number is at most `C ^ 2`. Since the harmonic series diverges, no single `C` can
serve every `M`. -/
theorem harmonic_le_of_centredMult (M : ℕ) (C : NNReal) (hC : C ≠ 0) {U' : Set E3}
    (hmeas : MeasurableSet U') (hsub : U' ⊆ shadeSet M)
    (hiv : ∀ x ∈ U', ∀ y ∈ U',
      volume (U' ∩ Metric.ball x 1) ≤ (C : ENNReal) * volume (U' ∩ Metric.ball y 1))
    (hvi : (C : ENNReal)⁻¹ * volume (shadeSet M) ≤ volume U') :
    (∑ k ∈ Finset.range M, 1 / ((k : ℝ) + 1)) ≤ (C : ℝ) ^ 2 := by
  classical
  set H : ℝ := ∑ k ∈ Finset.range M, 1 / ((k : ℝ) + 1) with hH
  have hHnonneg : 0 ≤ H := Finset.sum_nonneg fun k _ => by positivity
  set m : ℕ → ENNReal := fun k => volume (U' ∩ blob k) with hmdef
  have hCne : (C : ENNReal) ≠ 0 := by simpa using hC
  have hCtop : (C : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  -- the mass of `U'` splits over the blobs
  have hdecomp : volume U' = ∑ k ∈ Finset.range M, m k := by
    have hUeq : U' = ⋃ k ∈ Finset.range M, (U' ∩ blob k) := by
      rw [← Set.inter_iUnion₂]
      exact (Set.inter_eq_self_of_subset_left hsub).symm
    rw [hUeq]
    exact measure_biUnion_finset
      (fun k _ l _ hkl => (blob_disjoint hkl).mono Set.inter_subset_right
        Set.inter_subset_right)
      (fun k _ => hmeas.inter (measurableSet_blob k))
  have hmle : ∀ k, m k ≤ volume (blob k) := fun k => measure_mono Set.inter_subset_right
  -- the final numeric step, from `volume U' ≤ C * massUnit`
  have hfinal : volume U' ≤ (C : ENNReal) * massUnit → H ≤ (C : ℝ) ^ 2 := by
    intro hbound
    have h1 : volume (shadeSet M) ≤ (C : ENNReal) * ((C : ENNReal) * massUnit) :=
      (ENNReal.inv_mul_le_iff hCne hCtop).mp (le_trans hvi hbound)
    rw [volume_shadeSet, massUnit] at h1
    have h2 : ENNReal.ofReal ((1 / 64 : ℝ) * H) ≤
        ENNReal.ofReal ((C : ℝ) ^ 2 * (1 / 64 : ℝ)) := by
      have hrw : (C : ENNReal) * ((C : ENNReal) * (ENNReal.ofReal (1 / 64 : ℝ) * v0))
          = ENNReal.ofReal ((C : ℝ) ^ 2 * (1 / 64 : ℝ)) * v0 := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow C.coe_nonneg,
          ENNReal.ofReal_coe_nnreal]
        ring
      rw [hrw] at h1
      exact (ENNReal.mul_le_mul_iff_left v0_pos.ne' v0_ne_top).mp h1
    have h3 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h2
    linarith
  -- either `U'` is null, or the pigeonhole bites
  set S := (Finset.range M).filter (fun k => m k ≠ 0) with hSdef
  rcases S.eq_empty_or_nonempty with hSempty | hSne
  · refine hfinal ?_
    have : volume U' = 0 := by
      rw [hdecomp]
      refine Finset.sum_eq_zero fun k hk => ?_
      by_contra hne
      have : k ∈ S := Finset.mem_filter.mpr ⟨hk, hne⟩
      rw [hSempty] at this
      simp at this
    simp [this]
  · set kstar := S.max' hSne with hkstar
    have hkstarS : kstar ∈ S := S.max'_mem hSne
    have hkstarne : m kstar ≠ 0 := (Finset.mem_filter.mp hkstarS).2
    obtain ⟨y, hy⟩ : (U' ∩ blob kstar).Nonempty := nonempty_of_measure_ne_zero hkstarne
    -- every surviving blob mass is at most `C` times the mass of the maximal-index one
    have hkey : ∀ k ∈ S, m k ≤ (C : ENNReal) * m kstar := by
      intro k hk
      obtain ⟨x, hx⟩ : (U' ∩ blob k).Nonempty :=
        nonempty_of_measure_ne_zero (Finset.mem_filter.mp hk).2
      have h1 := hiv x hx.1 y hy.1
      rwa [inter_ball_eq hsub hx.2, inter_ball_eq hsub hy.2] at h1
    -- the index of the maximal blob is bounded by the mass unit
    have hstarmass : ((kstar : ENNReal) + 1) * m kstar ≤ massUnit := by
      refine le_trans ?_ (le_of_eq (succ_mul_volume_blob kstar))
      exact mul_le_mul_right (hmle kstar) _
    have hSsub : S ⊆ Finset.range (kstar + 1) := fun k hk =>
      Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_max' S k hk))
    have hcard : (S.card : ENNReal) ≤ (kstar : ENNReal) + 1 := by
      have h1 : S.card ≤ kstar + 1 := by simpa using Finset.card_le_card hSsub
      exact_mod_cast h1
    refine hfinal ?_
    have hsum : volume U' = ∑ k ∈ S, m k := by
      rw [hdecomp, hSdef]
      refine (Finset.sum_filter_ne_zero _).symm
    calc volume U' = ∑ k ∈ S, m k := hsum
      _ ≤ S.card • ((C : ENNReal) * m kstar) :=
          Finset.sum_le_card_nsmul S m _ hkey
      _ = (S.card : ENNReal) * ((C : ENNReal) * m kstar) := by simp
      _ ≤ ((kstar : ENNReal) + 1) * ((C : ENNReal) * m kstar) := by gcongr
      _ = (C : ENNReal) * (((kstar : ENNReal) + 1) * m kstar) := by ring
      _ ≤ (C : ENNReal) * massUnit := by gcongr

/-! ### The convex body and the shaded body -/

lemma measurableSet_shadeSet (M : ℕ) : MeasurableSet (shadeSet M) := by
  unfold shadeSet
  exact Finset.measurableSet_biUnion _ fun k _ => measurableSet_blob k

/-- The single body of the counterexample. -/
noncomputable def carrierBody (M : ℕ) : ConvexSpaceBody E3 :=
  ⟨capsule M, (convex_capsule M).isConvexSet, isCompact_capsule M, capsule_nonempty M⟩

@[simp] lemma carrierBody_carrier (M : ℕ) : (carrierBody M).carrier = capsule M := rfl

/-- The single shaded body of the counterexample. -/
noncomputable def shadedBody (M : ℕ) : ShadedBody E3 :=
  { toConvexSpaceBody := carrierBody M
    shade := shadeSet M
    measurableSet_shade := measurableSet_shadeSet M
    shade_subset := shadeSet_subset_capsule M }

@[simp] lemma shadedBody_shade (M : ℕ) : (shadedBody M).shade = shadeSet M := rfl

@[simp] lemma shadedBody_body (M : ℕ) : (shadedBody M).toConvexSpaceBody = carrierBody M := rfl

lemma volume_capsule_ne_top (M : ℕ) : volume (capsule M) ≠ ⊤ :=
  (isCompact_capsule M).measure_lt_top.ne

lemma volume_capsule_ne_zero (M : ℕ) : volume (capsule M) ≠ 0 := by
  refine ne_of_gt (lt_of_lt_of_le ?_ (measure_mono (closedBall_subset_capsule M)))
  exact measure_closedBall_pos _ _ (by norm_num)

lemma volume_shadeSet_pos {M : ℕ} (hM : 0 < M) : 0 < volume (shadeSet M) := by
  refine lt_of_lt_of_le ?_ (measure_mono (fun z hz => Set.mem_iUnion₂.mpr
    ⟨0, Finset.mem_range.mpr hM, hz⟩) : volume (blob 0) ≤ volume (shadeSet M))
  exact measure_closedBall_pos _ _ (rad_pos 0)

lemma volume_shadeSet_ne_top (M : ℕ) : volume (shadeSet M) ≠ ⊤ :=
  ne_top_of_le_ne_top (volume_capsule_ne_top M) (measure_mono (shadeSet_subset_capsule M))

/-- A one-element family is `1`-Frostman in its own body. -/
lemma isFrostmanIn_self {K : ConvexSpaceBody E3} (h0 : volume K.carrier ≠ 0)
    (htop : volume K.carrier ≠ ⊤) :
    ConvexSpaceBody.IsFrostmanIn (Finset.univ : Finset Unit) (fun _ => K) K 1 := by
  classical
  intro K' hK'
  have hself : Kakeya.densityIn (Finset.univ : Finset Unit) (fun _ => K) K = 1 := by
    have hfil : (Finset.univ.filter (fun _ : Unit => K ≤ K)) = Finset.univ := by
      simp
    simp only [Kakeya.densityIn, hfil]
    rw [Finset.sum_const, Finset.card_univ]
    simp [ENNReal.div_self h0 htop]
  rw [hself, one_mul]
  by_cases hle : K ≤ K'
  · have : K' = K := le_antisymm hK' hle
    subst this
    simp only [Kakeya.densityIn]
    have hfil : (Finset.univ.filter (fun _ : Unit => K' ≤ K')) = Finset.univ := by simp
    rw [hfil, Finset.sum_const, Finset.card_univ]
    simp [ENNReal.div_self h0 htop]
  · have hfil : (Finset.univ.filter (fun _ : Unit => K ≤ K')) = ∅ := by
      simp [hle]
    simp only [Kakeya.densityIn, hfil]
    simp

/-- The shortest affine scale of the refuting body is at least `1 / 2 = δ`: the capsule is a
`1/2`-neighbourhood of a segment, so its rank-`2` thickness is exactly `1/2`
(`thickness_capsule_le`, `thickness_capsule_ge`) and `Metric.ethickness` is antitone in the rank.

This is the `le_scale` field of `ShadedBody.FactorFamily.InnerIsDiscretizedAtScale`, the second
hypothesis the repair of `Kakeya.ThinCase.factoringApply` added. The refuting configuration
satisfies it at `δ₀ = δ`, so the refutation below is *stronger* than before: the statement is
false even with the discretization hypothesis in hand at the full scale `δ`, the missing
hypothesis being `subset_unitBall` alone. -/
lemma scale_capsule_ge (M : ℕ) :
    ((1 / 2 : NNReal) : ENNReal) ≤ Metric.ethickness.scale ℝ (capsule M) := by
  rw [Metric.ethickness.le_scale_iff]
  intro k
  have hk2 : (k : ℕ) ≤ 2 := by
    have hlt : (k : ℕ) < Module.finrank ℝ E3 := k.isLt
    have h3 : Module.finrank ℝ E3 = 3 := finrank_euclideanSpace_fin
    omega
  refine le_trans ?_ (Metric.ethickness_antitone (𝕜 := ℝ) (s := capsule M) hk2)
  rw [Metric.ethickness_thickness' (isCompact_capsule M).isBounded]
  have h := thickness_capsule_ge M
  have hcoe : ((1 / 2 : NNReal) : ENNReal) = ENNReal.ofReal ((1 : ℝ) / 2) := by
    rw [← ENNReal.ofReal_coe_nnreal]; norm_num
  rw [hcoe]
  exact ENNReal.ofReal_le_ofReal h

/-! ### The statement under test -/

universe u v w

/-- The statement of `Kakeya.ThinCase.factoringApply` **without the localisation hypothesis**,
all binders explicit. This is the form the declaration had when the refutation below was
written, and it is the form `factoringApply_refuted` refutes.

The declaration now carries one further hypothesis,
`hloc : ∃ z, ∀ j ∈ bodies, (Wb j).carrier ⊆ Metric.closedBall z 1`. That `hloc` is the *only*
difference is not a claim of the prose: `statement_of_universal_loc` below derives this exact
`Prop` from the current declaration by supplying `hloc` and nothing else, so it typechecks only
as long as that remains true.

**Conjunct (i) now reads `δ^{3η}`, and the refutation is untouched by that.** The exponent
followed `Kakeya.ThinCase.ThinBall.fullness_bodies` from `2η` to `3η` (see that field for why),
and `statement_of_universal_loc` is what forces this `Prop` to track it. The refutation
`factoringApply_refuted` does **not** read conjunct (i) at all — it discards it with a `-` in
its own destructuring, which is the compiler-checked form of that claim — so it refutes the
statement at *every* output exponent, the old `2η` included: the `2η` form implies this one,
since `δ ≤ 1`. Weakening conjunct (i) therefore cannot retire the refutation, and no separate
identification of the old form is needed. -/
def FactoringApplyStatement : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E], Module.finrank ℝ E = 3 →
  ∀ {σ : Type v} {ω : Type w} [DecidableEq ω] (segs : Finset σ) (Y : σ → ShadedBody E)
    (bodies : Finset ω) (Wb : ω → ConvexSpaceBody E) (blk : σ → ω)
    {δ w₁ : NNReal} {η : ℝ} {CF Cfull Ccore : NNReal},
    0 < δ → δ ≤ w₁ → w₁ ≤ 1 → (0:ℝ) ≤ η → 1 ≤ CF → 2 ≤ Ccore →
    (ShadedBody.outerFactoringFamily_refinement.c 3 segs.card δ)⁻¹ ≤ Ccore →
    ShadedBody.outerFactoringFamily_outerConstMultFat.c 3 bodies.card δ ≤ Ccore →
    ((Nat.log 2 bodies.card + 1 : ℕ) : NNReal) ≤ Ccore →
    ((Nat.log 2 ⌈CF⌉₊ + 1 : ℕ) : NNReal) ≤ Ccore →
    (∀ p ∈ segs, blk p ∈ bodies) →
    (∀ p ∈ segs, (Y p).toConvexSpaceBody ≤ Wb (blk p)) →
    (∀ p ∈ segs, ∀ q ∈ segs,
      Metric.thickness ℝ (Y p).carrier ≤ 2 • Metric.thickness ℝ (Y q).carrier) →
    (∀ j ∈ bodies, ConvexSpaceBody.IsFrostmanIn (segs.filter fun p => blk p = j)
      (fun p => (Y p).toConvexSpaceBody) (Wb j) CF) →
    (∀ j ∈ bodies,
      Metric.thickness ℝ (Wb j).carrier (Module.finrank ℝ E - 1) ≤ 2 * w₁ ∧
        (w₁ : ℝ) ≤ 2 * Metric.thickness ℝ (Wb j).carrier (Module.finrank ℝ E - 1)) →
    ∀ {δ₀ : NNReal}, 0 < δ₀ → δ₀ ≤ w₁ →
    (∀ p ∈ segs, (δ₀ : ENNReal) ≤ Metric.ethickness.scale ℝ (Y p).carrier) →
    (ShadedBody.outerFactoringFamily_refinement.c 3 segs.card δ₀)⁻¹ ≤ Ccore →
    ShadedBody.outerFactoringFamily_outerConstMultFat.c 3 bodies.card δ₀ ≤ Ccore →
    Kakeya.ThinCase.thinEnvelopeTerm 3 segs.card bodies.card CF w₁ ≤ Ccore →
    (∀ p ∈ segs,
      (δ : ENNReal) ^ η * volume (Y p).carrier ≤ (Cfull : ENNReal) * volume (Y p).shade) →
    ((δ : ENNReal) ^ η ≤ (Cfull : ENNReal) * (ShadedBody.fullness segs Y : ENNReal)) →
    ∃ (segs' : Finset σ) (bodies' : Finset ω)
      (Y' : σ → ShadedBody E) (W : ω → ShadedBody E),
      segs' ⊆ segs ∧ bodies' ⊆ bodies ∧
      (∀ p ∈ segs, (Y' p).toConvexSpaceBody = (Y p).toConvexSpaceBody) ∧
      (∀ p ∈ segs', (Y' p).shade ⊆ (Y p).shade) ∧
      (∀ j ∈ bodies', Wb j ≤ (W j).toConvexSpaceBody) ∧
      (∀ j ∈ bodies', (W j).toConvexSpaceBody ≤ (Wb j).cthickening (Wb j).scale) ∧
      ((δ : ENNReal) ^ (3 * η) ≤
        (factoringApplyConstant CF Cfull Ccore : ENNReal) *
          (ShadedBody.fullness bodies' W : ENNReal)) ∧
      (∀ p ∈ segs', ∀ x ∈ (Y' p).shade, blk p ∈ bodies' ∧ x ∈ (W (blk p)).shade) ∧
      (ShadedBody.HasCConstantMultiplicity bodies' W (factoringApplyConstant CF Cfull Ccore)) ∧
      (∃ μinner : NNReal, ∀ j ∈ bodies',
        ∀ x ∈ ShadedBody.iUnionShade (segs'.filter fun p => blk p = j) Y',
          (ShadedBody.pointwiseMultiplicity (segs'.filter fun p => blk p = j) Y' x : ENNReal) ≤
              (factoringApplyConstant CF Cfull Ccore : ENNReal) * μinner ∧
            (μinner : ENNReal) ≤ (factoringApplyConstant CF Cfull Ccore : ENNReal) *
              (ShadedBody.pointwiseMultiplicity (segs'.filter fun p => blk p = j) Y' x :
                ENNReal)) ∧
      (∀ x ∈ ShadedBody.iUnionShade bodies' W, ∀ y ∈ ShadedBody.iUnionShade bodies' W,
        volume (ShadedBody.iUnionShade segs' Y' ∩ Metric.ball x (w₁ : ℝ)) ≤
          (factoringApplyConstant CF Cfull Ccore : ENNReal) *
            volume (ShadedBody.iUnionShade segs' Y' ∩ Metric.ball y (w₁ : ℝ))) ∧
      (∀ j ∈ bodies', (W j).shade ⊆
        Metric.cthickening (2 * Metric.thickness ℝ (Wb j).carrier (Module.finrank ℝ E - 1))
          (ShadedBody.iUnionShade (segs'.filter fun p => blk p = j) Y')) ∧
      ((factoringApplyConstant CF Cfull Ccore : ENNReal)⁻¹ *
          ∑ p ∈ segs, volume (Y p).shade ≤
        ∑ p ∈ segs', volume (Y' p).shade)

/-- **Tripwire / fidelity check.** Granting the localisation hypothesis universally and for
free, the current `Kakeya.ThinCase.factoringApply` *is* `FactoringApplyStatement`: every other
argument — the five `Ccore` envelope bounds, the discretization scale `δ₀` with its two bounds
and `hscale`, `hdims`, `hFr`, the width clause, `hdens` and `hfullness` — is passed through
verbatim. So `hloc` is the only hypothesis granted rather than supplied, and the refutation
below still bites on everything else.

`hLoc` is of course false — `not_subset_closedBall_one` exhibits a family violating it — so
combining this with `factoringApply_refuted` merely reproves `¬ hLoc`, which is sound. -/
theorem statement_of_universal_loc
    (hLoc : ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {ω : Type w}
      (bodies : Finset ω) (Wb : ω → ConvexSpaceBody E),
      ∃ z : E, ∀ j ∈ bodies, (Wb j).carrier ⊆ Metric.closedBall z 1) :
    FactoringApplyStatement.{u, v, w} := by
  intro E instE₁ instE₂ instE₃ instE₄ instE₅ hdim σ ω instω segs Y bodies Wb blk
    δ w₁ η CF Cfull Ccore hδ hδw₁ hw₁one hη hCF hCcore2 hCcoreRef hCcoreMult hCcoreDyad
    hCcoreFrost
    hblk hle hdims hFr hwd δ₀ hδ₀ hδ₀w₁ hscale hCcoreRef₀ hCcoreMult₀ hCcoreNet hdens hfull
  exact Kakeya.ThinCase.factoringApply hdim segs Y bodies Wb blk hδ hδw₁ hw₁one hη hCF hCcore2
    hCcoreRef hCcoreMult hCcoreDyad hCcoreFrost hblk hle hdims hFr hwd (hLoc bodies Wb)
    hδ₀ hδ₀w₁ hscale hCcoreRef₀ hCcoreMult₀ hCcoreNet hdens hfull

/-! ### The refutation -/

lemma fullness_config (M : ℕ) :
    (ShadedBody.fullness (Finset.univ : Finset Unit) (fun _ => shadedBody M) : ENNReal)
      = volume (shadeSet M) / volume (capsule M) := by
  rw [ShadedBody.coe_fullness]
  simp [ShadedBody.fullness']

lemma fullness_ne_zero {M : ℕ} (hM : 0 < M) :
    ShadedBody.fullness (Finset.univ : Finset Unit) (fun _ => shadedBody M) ≠ 0 := by
  intro h
  have h1 : (ShadedBody.fullness (Finset.univ : Finset Unit) (fun _ => shadedBody M) : ENNReal)
      = 0 := by rw [h]; simp
  rw [fullness_config] at h1
  rw [ENNReal.div_eq_zero_iff] at h1
  rcases h1 with h1 | h1
  · exact (volume_shadeSet_pos hM).ne' h1
  · exact volume_capsule_ne_top M h1

lemma exists_eta {f : NNReal} (hf : f ≠ 0) :
    ∃ n : ℕ, ((1 / 2 : NNReal) : ENNReal) ^ ((n : ℕ) : ℝ) ≤ (f : ENNReal) := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < (f : ℝ) by positivity)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  refine ⟨n, ?_⟩
  rw [ENNReal.rpow_natCast, ← ENNReal.coe_pow]
  refine ENNReal.coe_le_coe.mpr ?_
  rw [← NNReal.coe_le_coe]
  push_cast
  linarith

/-- The *pointwise* form of the density hypothesis at the configuration, which is the same
statement here because there is only one segment: `δ^η |carrier| ≤ Cfull |shade|` at
`Cfull = 1`. -/
lemma dens_of_eta {M n : ℕ}
    (hn : ((1 / 2 : NNReal) : ENNReal) ^ ((n : ℕ) : ℝ)
      ≤ (ShadedBody.fullness (Finset.univ : Finset Unit) (fun _ => shadedBody M) : ENNReal)) :
    ((1 / 2 : NNReal) : ENNReal) ^ ((n : ℕ) : ℝ) * volume (capsule M)
      ≤ ((1 : NNReal) : ENNReal) * volume (shadeSet M) := by
  rw [fullness_config] at hn
  rw [show ((1 : NNReal) : ENNReal) = 1 from by simp, one_mul]
  calc ((1 / 2 : NNReal) : ENNReal) ^ ((n : ℕ) : ℝ) * volume (capsule M)
      ≤ (volume (shadeSet M) / volume (capsule M)) * volume (capsule M) := by
        gcongr
    _ = volume (shadeSet M) :=
        ENNReal.div_mul_cancel (volume_capsule_ne_zero M) (volume_capsule_ne_top M)

lemma exists_harmonic_gt (c : ℝ) : ∃ M : ℕ, c < ∑ k ∈ Finset.range M, 1 / ((k : ℝ) + 1) := by
  have h := Real.tendsto_sum_range_one_div_nat_succ_atTop
  rw [tendsto_atTop_atTop] at h
  obtain ⟨M, hM⟩ := h (c + 1)
  exact ⟨M, by linarith [hM M le_rfl]⟩

/-- **`Kakeya.ThinCase.factoringApply` is false as stated.**

Clause (iv) — the centred multiplicity comparison at *equal* radii `w₁` — and clause (vi) — the
`C⁻¹` mass retention — are jointly unachievable with the ball-independent constant
`factoringApplyConstant CF Cfull Ccore`, whose only cardinality inputs are `segs.card` and
`bodies.card`.

The witness uses **one** segment inside **one** body: a capsule of thickness `1/2` around a long
segment of the first coordinate axis, whose shading is the union of `M` pairwise `2`-separated
balls with harmonic masses `|blob k| = massUnit / (k+1)`. Every hypothesis is met with `δ = 1/2`,
`w₁ = 1`, `CF = Cfull = 1` and `Ccore = factoringApplyCore 3 1 1 (1/2)`, and neither `segs.card`
nor `bodies.card` sees `M`, so the output constant `C` is one fixed number for every `M`. Clause
(iv) forces the retained blob masses to be pairwise comparable up to `C`, which caps the retained
mass at `C * massUnit`; clause (vi) demands at least `C⁻¹ * massUnit * H_M`. Hence `H_M ≤ C ^ 2`
for every `M`, and the harmonic series diverges. -/
theorem factoringApply_refuted : ¬ FactoringApplyStatement.{0, 0, 0} := by
  classical
  intro H
  set Ccore : NNReal := max (factoringApplyCore 3 1 1 (1 / 2 : NNReal))
    (Kakeya.ThinCase.thinEnvelopeTerm 3 1 1 1 1) with hCcoreDef
  set C : NNReal := factoringApplyConstant 1 1 Ccore with hCdef
  obtain ⟨M, hM⟩ := exists_harmonic_gt ((C : ℝ) ^ 2)
  have hMpos : 0 < M := by
    rcases Nat.eq_zero_or_pos M with h | h
    · exfalso; rw [h] at hM; simp at hM; nlinarith [hM, sq_nonneg (C : ℝ)]
    · exact h
  obtain ⟨n, hn⟩ := exists_eta (fullness_ne_zero hMpos)
  have hdensPt := dens_of_eta (M := M) (n := n) (by simpa using hn)
  -- the hypotheses of `factoringApply` at the harmonic configuration
  have hcard : (Finset.univ : Finset Unit).card = 1 := by simp
  obtain ⟨hc2, hcref, hcmult, hcdyad⟩ := factoringApplyCore_spec 3 1 1 (1 / 2 : NNReal)
  have hdim : Module.finrank ℝ E3 = 3 := finrank_euclideanSpace_fin
  have hthick2 : Module.finrank ℝ E3 - 1 = 2 := by rw [hdim]
  obtain ⟨segs', bodies', Y', W, h_segs, h_bodies, h_car, h_shade, h_WbLe, h_WleCth,
      -- conjunct (i) is deliberately **discarded**: the refutation uses (iv) and (vi) only, so
      -- it bites at every output exponent, and in particular at the old `2 * η`
      -, h_contain, h_cmult, h_inner, h_centw1, h_Wshade, h_refsum⟩ :=
    H (E := E3) hdim (Finset.univ : Finset Unit) (fun _ => shadedBody M)
      (Finset.univ : Finset Unit) (fun _ => carrierBody M) (fun _ => ())
      (δ := 1 / 2) (w₁ := 1) (η := (n : ℝ)) (CF := 1) (Cfull := 1) (Ccore := Ccore)
      (by norm_num) (by norm_num) le_rfl (Nat.cast_nonneg n) le_rfl
      (le_trans hc2 (le_max_left _ _))
      (by rw [hcard]; exact le_trans hcref (le_max_left _ _))
      (by rw [hcard]; exact le_trans hcmult (le_max_left _ _))
      (by rw [hcard]; exact le_trans hcdyad (le_max_left _ _))
      (le_trans (le_trans (by norm_num) hc2) (le_max_left _ _))
      (fun _ _ => Finset.mem_univ _) (fun _ _ => le_rfl)
      (fun p _ q _ i => by
        simp only [Pi.smul_apply, nsmul_eq_mul, Nat.cast_ofNat]
        nlinarith [Metric.thickness_nonneg (𝕜 := ℝ) ((shadedBody M).carrier) i])
      (fun j _ => by
        have hfil : (Finset.univ.filter (fun _ : Unit => (() : Unit) = j)) = Finset.univ := by
          ext p; simp
        rw [hfil]
        exact isFrostmanIn_self (volume_capsule_ne_zero M) (volume_capsule_ne_top M))
      (fun j _ => by
        rw [hthick2]
        refine ⟨?_, ?_⟩
        · change Metric.thickness ℝ (capsule M) 2 ≤ 2 * ((1 : NNReal) : ℝ)
          have := thickness_capsule_le M
          push_cast
          linarith
        · change ((1 : NNReal) : ℝ) ≤ 2 * Metric.thickness ℝ (capsule M) 2
          have := thickness_capsule_ge M
          push_cast
          linarith)
      (δ₀ := 1 / 2) (by norm_num) (by norm_num) (fun p _ => scale_capsule_ge M)
      (by rw [hcard]; exact le_trans hcref (le_max_left _ _))
      (by rw [hcard]; exact le_trans hcmult (le_max_left _ _))
      (le_max_right _ _)
      (fun p _ => by simpa using hdensPt)
      (by simpa using hn)
  rw [← hCdef] at h_refsum h_centw1
  -- `C` is not `0`
  have hCne : C ≠ 0 := by
    rw [hCdef]
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_factoringApplyConstant))
  have hCneE : (C : ENNReal) ≠ 0 := by simpa using hCne
  have hCtop : (C : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  -- the left-hand side of clause (vi)
  have hlhs : ∑ p ∈ (Finset.univ : Finset Unit), volume ((shadedBody M).shade)
      = volume (shadeSet M) := by simp
  by_cases hmem : (() : Unit) ∈ segs'
  · -- the retained family is the whole (one-element) family
    have hsegs'univ : segs' = Finset.univ := by
      refine Finset.eq_univ_iff_forall.mpr fun p => ?_
      cases p; exact hmem
    set U' : Set E3 := (Y' ()).shade with hU'
    have hUnion : ShadedBody.iUnionShade segs' Y' = U' := by
      rw [hsegs'univ]; ext z
      simp only [ShadedBody.iUnionShade, Set.mem_iUnion, Finset.mem_univ, exists_prop,
        true_and, hU']
      exact ⟨fun ⟨i, hi⟩ => by cases i; exact hi, fun h => ⟨(), h⟩⟩
    have hsub : U' ⊆ shadeSet M := by
      have := h_shade () (hsegs'univ ▸ Finset.mem_univ ())
      simpa using this
    have hvi : (C : ENNReal)⁻¹ * volume (shadeSet M) ≤ volume U' := by
      have h1 : ∑ p ∈ segs', volume (Y' p).shade = volume U' := by
        rw [hsegs'univ]; simp [hU']
      rw [h1, hlhs] at h_refsum
      exact h_refsum
    have hiv : ∀ x ∈ U', ∀ y ∈ U',
        volume (U' ∩ Metric.ball x 1) ≤ (C : ENNReal) * volume (U' ∩ Metric.ball y 1) := by
      intro x hx y hy
      have hxW : x ∈ ShadedBody.iUnionShade bodies' W := by
        obtain ⟨hb, hxs⟩ := h_contain () (hsegs'univ ▸ Finset.mem_univ ()) x hx
        exact Set.mem_iUnion₂.mpr ⟨(), hb, hxs⟩
      have hyW : y ∈ ShadedBody.iUnionShade bodies' W := by
        obtain ⟨hb, hys⟩ := h_contain () (hsegs'univ ▸ Finset.mem_univ ()) y hy
        exact Set.mem_iUnion₂.mpr ⟨(), hb, hys⟩
      have := h_centw1 x hxW y hyW
      rwa [hUnion, NNReal.coe_one] at this
    have := harmonic_le_of_centredMult M C hCne (Y' ()).measurableSet_shade hsub hiv hvi
    linarith
  · -- the retained family is empty, and clause (vi) fails outright
    have hempty : segs' = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun p hp => hmem ?_
      cases p; exact hp
    rw [hempty] at h_refsum
    simp only [Finset.sum_empty, nonpos_iff_eq_zero] at h_refsum
    rw [hlhs] at h_refsum
    rcases mul_eq_zero.mp h_refsum with h | h
    · exact (ENNReal.inv_ne_zero.mpr hCtop) h
    · exact (volume_shadeSet_pos hMpos).ne' h

/-! ### Which hypothesis of GWZ Proposition 5.1 the configuration violates -/

lemma ctr_mem_capsule {k M : ℕ} (h : k ≤ M) : ctr k ∈ capsule M :=
  Metric.self_subset_cthickening _ (ctr_mem_spine h)

/-- **The exact hypothesis of GWZ Proposition 5.1 that `Kakeya.ThinCase.factoringApply` dropped.**

The pipeline behind `ShadedBody.outerFactoringFamily` — and hence every one of the seven items of
GWZ Proposition 5.1, item 7 (`ShadedBody.outerFactoringFamily_avgMultOnBalls`) included — runs
under `ShadedBody.FactorFamily.InnerIsDiscretizedAtScale δ`, whose first field
`ConvexSpaceBody.IsDiscretizedAtScale.subset_unitBall` puts **every** body of the family inside
the closed unit ball. With `δ ≤ w₁`, that hypothesis caps the number of `w₁`-balls needed to
cover the shaded union by `(1 + 4/δ) ^ n`, so the dyadic mass pigeonhole of Step 5
(`Kakeya.factoringStep5SelfPigeonholeConstant`) costs only `O(n log δ⁻¹)` — subpolynomial in
`δ⁻¹`, hence inside the `Ccore` budget.

`Kakeya.ThinCase.factoringApply` carries no such hypothesis, and the refuting configuration is
precisely one that violates it: the capsule has diameter `2 M`. -/
theorem not_subset_closedBall_one {M : ℕ} (hM : 2 ≤ M) (x : E3) :
    ¬ ((carrierBody M).carrier ⊆ Metric.closedBall x 1) := by
  intro h
  have h0 : ctr 0 ∈ Metric.closedBall x 1 := h (ctr_mem_capsule (Nat.zero_le M))
  have hM' : ctr M ∈ Metric.closedBall x 1 := h (ctr_mem_capsule le_rfl)
  have hd : dist (ctr 0) (ctr M) ≤ 2 := by
    refine le_trans (dist_triangle (ctr 0) x (ctr M)) ?_
    have h1 := Metric.mem_closedBall.mp h0
    have h2 := Metric.mem_closedBall.mp hM'
    rw [dist_comm x (ctr M)]
    linarith
  rw [dist_ctr] at hd
  have hMR : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  rw [abs_of_nonpos (by push_cast; linarith)] at hd
  push_cast at hd
  linarith

end Kakeya.ThinCase.Refute

namespace Kakeya.ThinCase.Localise

open MeasureTheory Metric Set ShadedBody

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **The refinement that makes clause (iv) available at equal radii, and its exact cost.**

Given any finite cover of `U` by the half-balls of a net `T`, keeping the *heaviest* half-ball
alone produces a refinement on which the centred multiplicity comparison at radius `w₁` holds
with constant `1` — both sides are then equal to the whole retained mass, because a set of
diameter `< w₁` lies inside the `w₁`-ball around each of its own points. The cost is exactly
`T.card`, the covering number of `U` at scale `w₁ / 2`.

This is the positive half of the analysis of clause (iv) of `Kakeya.ThinCase.factoringApply`:
the clause *is* obtainable, at a price equal to the covering number of the shaded union at scale
`w₁`. `Kakeya.ThinCase.Refute.factoringApply_refuted` is the negative half: a constant that does
not see that covering number — and `factoringApplyConstant CF Cfull Ccore` sees only `CF`,
`Cfull`, `segs.card` and `bodies.card` — cannot pay it. -/
theorem exists_localised_refinement {U : Set E} {T : Finset E} (hT : T.Nonempty) {w₁ : ℝ}
    (hcover : U ⊆ ⋃ c ∈ T, Metric.ball c (w₁ / 2)) :
    ∃ c₀ ∈ T,
      ((T.card : ENNReal))⁻¹ * volume U ≤ volume (U ∩ Metric.ball c₀ (w₁ / 2)) ∧
      ∀ x ∈ U ∩ Metric.ball c₀ (w₁ / 2), ∀ y ∈ U ∩ Metric.ball c₀ (w₁ / 2),
        volume ((U ∩ Metric.ball c₀ (w₁ / 2)) ∩ Metric.ball x w₁) ≤
          volume ((U ∩ Metric.ball c₀ (w₁ / 2)) ∩ Metric.ball y w₁) := by
  classical
  obtain ⟨c₀, hc₀T, hc₀max⟩ :=
    T.exists_max_image (fun c => volume (U ∩ Metric.ball c (w₁ / 2))) hT
  refine ⟨c₀, hc₀T, ?_, ?_⟩
  · have hsum : volume U ≤ ∑ c ∈ T, volume (U ∩ Metric.ball c (w₁ / 2)) := by
      refine le_trans (measure_mono ?_) (measure_biUnion_finset_le T _)
      intro z hz
      obtain ⟨c, hc, hzc⟩ := Set.mem_iUnion₂.mp (hcover hz)
      exact Set.mem_iUnion₂.mpr ⟨c, hc, ⟨hz, hzc⟩⟩
    have hle : ∑ c ∈ T, volume (U ∩ Metric.ball c (w₁ / 2))
        ≤ (T.card : ENNReal) * volume (U ∩ Metric.ball c₀ (w₁ / 2)) := by
      refine le_trans (Finset.sum_le_card_nsmul T _ _ hc₀max) (le_of_eq ?_)
      simp
    refine (ENNReal.inv_mul_le_iff ?_ ?_).mpr (le_trans hsum hle)
    · simpa using (Finset.card_pos.mpr hT).ne'
    · exact ENNReal.natCast_ne_top _
  · have key : ∀ z ∈ U ∩ Metric.ball c₀ (w₁ / 2),
        (U ∩ Metric.ball c₀ (w₁ / 2)) ∩ Metric.ball z w₁ = U ∩ Metric.ball c₀ (w₁ / 2) := by
      intro z hz
      refine Set.inter_eq_self_of_subset_left fun u hu => ?_
      have h1 : dist u c₀ < w₁ / 2 := Metric.mem_ball.mp hu.2
      have h2 : dist c₀ z < w₁ / 2 := by
        rw [dist_comm]; exact Metric.mem_ball.mp hz.2
      exact Metric.mem_ball.mpr (lt_of_le_of_lt (dist_triangle u c₀ z) (by linarith))
    intro x hx y hy
    rw [key x hx, key y hy]

/-- **The covering-number loss is dimensional once the shaded union has diameter `≲ w₁`.**

If `U` lies in a ball of radius `R`, a maximal `w₁/2`-separated net of `U` has at most
`(1 + 4 R / w₁) ^ n` points, so the refinement of `exists_localised_refinement` retains at least
that fraction of the mass. This is precisely the hypothesis that
`Kakeya.ThinCase.factoringApply` is missing: its constant is a function of `CF`, `Cfull` and the
two cardinalities only, and nothing in its hypotheses bounds `R / w₁`. -/
theorem exists_localised_refinement_of_subset_ball {U : Set E} (hmeas : MeasurableSet U)
    (hbdd : Bornology.IsBounded U) {x₀ : E} {R w₁ : ℝ} (hw₁ : 0 < w₁) (hR : 0 ≤ R)
    (hUne : U.Nonempty) (hsub : U ⊆ Metric.ball x₀ R) :
    ∃ (U' : Set E) (L : ℕ), U' ⊆ U ∧ MeasurableSet U' ∧
      (L : ℝ) ≤ (1 + 4 * R / w₁) ^ Module.finrank ℝ E ∧
      (L : ENNReal)⁻¹ * volume U ≤ volume U' ∧
      (∀ x ∈ U', ∀ y ∈ U',
        volume (U' ∩ Metric.ball x w₁) ≤ volume (U' ∩ Metric.ball y w₁)) := by
  classical
  obtain ⟨T, hTU, hTsep, hTcover⟩ := Produce.exists_ballNet hbdd hw₁
  have hTne : T.Nonempty := by
    obtain ⟨z, hz⟩ := hUne
    obtain ⟨c, hc, -⟩ := Set.mem_iUnion₂.mp (hTcover hz)
    exact ⟨c, hc⟩
  obtain ⟨c₀, hc₀T, hmass, hmult⟩ := exists_localised_refinement hTne hTcover
  refine ⟨U ∩ Metric.ball c₀ (w₁ / 2), T.card, Set.inter_subset_left,
    hmeas.inter measurableSet_ball, ?_, hmass, hmult⟩
  have hcard := finite_and_card_le_of_separated (r := w₁ / 2) (R := R) (by positivity) hR x₀
    (N := (↑T : Set E)) hTsep (hTU.trans hsub)
  rw [Set.ncard_coe_finset] at hcard
  refine le_trans hcard.2 (le_of_eq ?_)
  congr 1
  field_simp
  ring

end Kakeya.ThinCase.Localise

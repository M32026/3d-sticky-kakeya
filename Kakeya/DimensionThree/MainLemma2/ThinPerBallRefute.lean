/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.ThinFactoringRefute
public import Kakeya.Thickness.Diam

/-!
# `Kakeya.ThinCase.perBall` inherits the defect of `Kakeya.ThinCase.factoringApply`

`Kakeya.ThinCase.factoringApply` is refuted in
`Kakeya/DimensionThree/MainLemma2/ThinFactoringRefute.lean`. This file settles that: **it is false**, for exactly the same reason.

## The two clauses

`Kakeya.ThinCase.ThinBall` carries the same pair of clauses that refuted `factoringApply`,
at the larger radius `A = rad C₀ a = max 1 (4 C₀) * a`:

* `ThinBall.centredMult` — `|U(𝕋_B, Y'_B) ∩ B(x, A)| ≤ C |U(𝕋_B, Y'_B) ∩ B(y, A)|` for all
  `x, y ∈ U(𝕋_B, Y'_B)`;
* `ThinBall.refine_S` together with `ThinBall.S_nonempty` — on the non-empty subfamily `𝒮_B`
  the refinement is termwise, `|Y_B(p)| ≤ C |Y'_B(p)|`.

With one segment (`segs.card = 1`) the second forces `C⁻¹ |Y(p)| ≤ |Y'(p)|`, so the pair is
exactly clauses (iv)+(vi) of `factoringApply` again, and
`Kakeya.ThinCase.perBallConstant C₀ CF c₁ Ccore D` sees only `C₀`, `CF`, `c₁`, `D` and — through
the four `Ccore` binders — `segs.card`, `bodies.card` and `δ`. None of them sees the covering
number of the shaded union at scale `A`, and nothing in `IsBallFactoring` bounds it: `thick`
and `body` pin the *shape* `(r₁, b, a)` of the bodies but leave `r₁` free, and
`IsBallFactoring` never says where in space the bodies are.

## The witness

One segment inside one body, so `segs.card = bodies.card = 1` and the output constant is one
fixed number `C := perBallConstant 2 1 1 (factoringApplyCore 3 1 1 (1/8)) 4`:

| object | value |
|---|---|
| carrier (= body) | `capsule M`, the closed `1/16`-neighbourhood of `[0, 2(M+1)] e₀` |
| shading | `⋃_{k < M} closedBall (2(k+1) e₀) ((1/32)(k+1)^(-1/3))` |
| scales | `δ = a = b = 1/8`, `w₁ = 1/8`, `r₁ = 2(M+1)`, `C₀ = 2`, `CF = c₁ = 1`, `D = 4` |

The capsule has `1`- and `2`-thickness exactly `1/16` and `0`-thickness in `[(M+1), 2(M+1) +
1/16]`, so `HasThicknesses (capsule M) 2 ![2(M+1), 1/8, 1/8]` holds for both `thick` and `body`
at once; a one-element family is `1`-Frostman in its own body; and the `δ`-ball covers of (T5)
are the balls of radius `1/8` about `(j/16) e₀`, which overlap at most `4`-fold. The blobs are
`2`-separated and have diameter `≤ 1/16`, so with

`A = rad 2 (1/8) = max 1 8 * (1/8) = 1`

the ball `B(x, A)` about a point of a blob meets the shading in that blob only. The masses are
harmonic, `(k+1) |blob k| = massUnit`, and the argument of
`Kakeya.ThinCase.Refute.harmonic_le_of_centredMult` — reproved here for these blobs — gives
`∑_{k<M} (k+1)⁻¹ ≤ C ^ 2` for every `M`.

## The repair, which is existing

`Kakeya.ThinCase.PerBallRefute.not_subset_closedBall_one` records that the witness violates the
localisation `(Wb j).carrier ⊆ closedBall z 1` for *every* centre `z`. So the hypothesis that
`Kakeya.ThinCase.factoringApply` is missing has to be visible at `Kakeya.ThinCase.perBall` too.
It now is: `perBall` carries

`hloc : ∃ z : E, ∀ j ∈ bodies, (Wb j).carrier ⊆ Metric.closedBall z 1`

as a binder — beside `hδw₁` and `hw₁one`, which are relocated hypotheses for the same reason:
`IsBallFactoring.body` pins the *shape* `(r₁, b, a)` of the bodies but leaves `r₁` free and
never says where in space they sit. The call site can discharge it, and does:
`Kakeya.ThinCase.thinSetupExists` passes it through and
`Kakeya.VeryNotSticky.exists_thinConfig` proves it from
`Kakeya.VeryNotSticky.BallData.bodies_subset_ball`, which already asserts
`(Wb j).carrier ⊆ closedBall (ctr B) r₁`, together with `r₁ = δ ^ exscal ≤ 1` (from
`VeryNotSticky.hδ1` and `VeryNotSticky.hexscal`). So this is a repair and not a shell game.

`statement_of_universal_loc` is the machine-checked form of "and `hloc` is the *only* thing that
was added": it derives `PerBallStatement` — the refuted, `hloc`-free `Prop` — from the current
`perBall` by granting `hloc` for free and passing every other argument through verbatim,
the two envelope bounds at the discretization scale `δ / C₀` included.

`PerBallStatement` refers to `Kakeya.ThinCase.IsBallFactoring` and
`Kakeya.ThinCase.DeltaBallCovers`, neither of which the repair touched, so the refutation below
continues to speak about the real hypotheses of the real lemma.
-/

@[expose] public section

namespace Kakeya.ThinCase.PerBallRefute

open MeasureTheory Metric Set ShadedBody Filter
open Kakeya.ThinCase.Refute (E3 ctr axisVec spine v0 v0_pos v0_ne_top one_le_succ dist_ctr
  two_le_dist_ctr ctr_eq_smul exists_harmonic_gt)

/-! ### The axis

The centres `Kakeya.ThinCase.Refute.ctr k = 2 (k+1) e₀` and the spine
`Kakeya.ThinCase.Refute.spine M = [0, ctr M]` are reused verbatim; only the *radii* change,
by a factor `8`, so that the blobs fit inside a capsule thin enough that
`rad C₀ a = 1` is still a locality radius. -/

lemma smul_axisVec_eq (t : ℝ) : t • axisVec = EuclideanSpace.single (0 : Fin 3) t := by
  unfold Kakeya.ThinCase.Refute.axisVec
  ext i
  simp

lemma dist_smul_axisVec (s t : ℝ) : dist (s • axisVec) (t • axisVec) = |s - t| := by
  rw [smul_axisVec_eq, smul_axisVec_eq]
  rw [show dist (EuclideanSpace.single (0 : Fin 3) s) (EuclideanSpace.single (0 : Fin 3) t)
      = dist s t from PiLp.dist_single_same 2 (fun _ => ℝ) _ _ _]
  exact Real.dist_eq _ _

lemma dist_smul_axisVec_zero (t : ℝ) : dist (t • axisVec) (0 : E3) = |t| := by
  have h0 : (0 : E3) = (0 : ℝ) • axisVec := by simp
  rw [h0, dist_smul_axisVec]
  simp

/-- Every point of the axis segment `[0, 2(M+1)] e₀` lies on the spine. -/
lemma smul_axisVec_mem_spine {M : ℕ} {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 2 * ((M : ℝ) + 1)) :
    t • axisVec ∈ spine M := by
  have hM : (0 : ℝ) < 2 * ((M : ℝ) + 1) := by positivity
  refine ⟨1 - t / (2 * ((M : ℝ) + 1)), t / (2 * ((M : ℝ) + 1)), ?_, ?_, by ring, ?_⟩
  · have : t / (2 * ((M : ℝ) + 1)) ≤ 1 := by rw [div_le_one hM]; exact h1
    linarith
  · positivity
  · rw [smul_zero, zero_add, ctr_eq_smul, smul_smul]
    congr 1
    field_simp

/-! ### The blobs -/

/-- The radius of the `k`-th blob: the radius of `Kakeya.ThinCase.Refute.blob k` divided by
`8`, so that the blob fits inside a capsule of thickness `1/16`. -/
noncomputable def brad (k : ℕ) : ℝ := (1 / 32 : ℝ) * ((k : ℝ) + 1) ^ (-(1 : ℝ) / 3)

/-- The `k`-th blob. -/
noncomputable def blob (k : ℕ) : Set E3 := Metric.closedBall (ctr k) (brad k)

/-- The shading of the counterexample: the union of the first `M` blobs. -/
noncomputable def shadeSet (M : ℕ) : Set E3 := ⋃ k ∈ Finset.range M, blob k

lemma brad_pos (k : ℕ) : 0 < brad k := by
  have h : (0 : ℝ) < ((k : ℝ) + 1) := by positivity
  have := Real.rpow_pos_of_pos h (-(1 : ℝ) / 3)
  unfold brad; positivity

lemma brad_le (k : ℕ) : brad k ≤ 1 / 32 := by
  have h1 : (1 : ℝ) ≤ ((k : ℝ) + 1) := one_le_succ k
  have := Real.rpow_le_one_of_one_le_of_nonpos h1 (by norm_num : (-(1:ℝ)/3) ≤ 0)
  unfold brad; nlinarith [this]

lemma brad_cube (k : ℕ) : brad k ^ 3 = (1 / 32768 : ℝ) / ((k : ℝ) + 1) := by
  have h : (0 : ℝ) < ((k : ℝ) + 1) := by positivity
  unfold brad
  rw [mul_pow]
  rw [← Real.rpow_natCast (((k : ℝ) + 1) ^ (-(1 : ℝ) / 3)) 3, ← Real.rpow_mul h.le]
  norm_num
  rw [Real.rpow_neg_one]
  ring

lemma dist_le_of_mem_blob {k : ℕ} {z : E3} (hz : z ∈ blob k) : dist z (ctr k) ≤ 1 / 32 :=
  le_trans (Metric.mem_closedBall.mp hz) (brad_le k)

/-- Locality at radius `1`: a point of `blob l` within distance `1` of a point of `blob k`
forces `k = l`. The blob centres are `2`-separated and the blobs have radius `≤ 1/32`. -/
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

lemma measurableSet_shadeSet (M : ℕ) : MeasurableSet (shadeSet M) := by
  unfold shadeSet
  exact Finset.measurableSet_biUnion _ fun k _ => measurableSet_blob k

/-! ### Volumes: the harmonic mass profile -/

lemma volume_blob (k : ℕ) :
    volume (blob k) = ENNReal.ofReal ((1 / 32768 : ℝ) / ((k : ℝ) + 1)) * v0 := by
  unfold blob Kakeya.ThinCase.Refute.v0
  rw [Measure.addHaar_closedBall volume (ctr k) (brad_pos k).le]
  congr 2
  rw [show Module.finrank ℝ E3 = 3 from finrank_euclideanSpace_fin]
  exact brad_cube k

/-- The common mass unit of the configuration: `(k+1) * |blob k|` for every `k`. -/
noncomputable def massUnit : ENNReal := ENNReal.ofReal (1 / 32768 : ℝ) * v0

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

lemma volume_shadeSet (M : ℕ) :
    volume (shadeSet M)
      = ENNReal.ofReal ((1 / 32768 : ℝ) * ∑ k ∈ Finset.range M, 1 / ((k : ℝ) + 1)) * v0 := by
  unfold shadeSet
  rw [measure_biUnion_finset (fun k _ l _ hkl => blob_disjoint hkl)
    (fun k _ => measurableSet_blob k)]
  rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg (fun k _ => by positivity), Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [volume_blob]
  congr 2
  ring

lemma volume_shadeSet_pos {M : ℕ} (hM : 0 < M) : 0 < volume (shadeSet M) := by
  refine lt_of_lt_of_le ?_ (measure_mono (fun z hz => Set.mem_iUnion₂.mpr
    ⟨0, Finset.mem_range.mpr hM, hz⟩) : volume (blob 0) ≤ volume (shadeSet M))
  exact measure_closedBall_pos _ _ (brad_pos 0)

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

/-- **The counting core.** A measurable subset `U'` of the harmonic configuration satisfying
the equal-radius centred multiplicity bound at radius `1` with constant `C`, and retaining at
least a `C⁻¹` fraction of the mass, forces `H_M ≤ C ^ 2`. -/
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
  have hfinal : volume U' ≤ (C : ENNReal) * massUnit → H ≤ (C : ℝ) ^ 2 := by
    intro hbound
    have h1 : volume (shadeSet M) ≤ (C : ENNReal) * ((C : ENNReal) * massUnit) :=
      (ENNReal.inv_mul_le_iff hCne hCtop).mp (le_trans hvi hbound)
    rw [volume_shadeSet, massUnit] at h1
    have h2 : ENNReal.ofReal ((1 / 32768 : ℝ) * H) ≤
        ENNReal.ofReal ((C : ℝ) ^ 2 * (1 / 32768 : ℝ)) := by
      have hrw : (C : ENNReal) * ((C : ENNReal) * (ENNReal.ofReal (1 / 32768 : ℝ) * v0))
          = ENNReal.ofReal ((C : ℝ) ^ 2 * (1 / 32768 : ℝ)) * v0 := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow C.coe_nonneg,
          ENNReal.ofReal_coe_nnreal]
        ring
      rw [hrw] at h1
      exact (ENNReal.mul_le_mul_iff_left v0_pos.ne' v0_ne_top).mp h1
    have h3 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h2
    linarith
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
    have hkey : ∀ k ∈ S, m k ≤ (C : ENNReal) * m kstar := by
      intro k hk
      obtain ⟨x, hx⟩ : (U' ∩ blob k).Nonempty :=
        nonempty_of_measure_ne_zero (Finset.mem_filter.mp hk).2
      have h1 := hiv x hx.1 y hy.1
      rwa [inter_ball_eq hsub hx.2, inter_ball_eq hsub hy.2] at h1
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

/-! ### The capsule -/

/-- The carrier of the counterexample: the closed `1/16`-neighbourhood of the spine. -/
noncomputable def capsule (M : ℕ) : Set E3 := Metric.cthickening (1 / 16) (spine M)

lemma isCompact_capsule (M : ℕ) : IsCompact (capsule M) :=
  isCompact_segment.cthickening

lemma convex_capsule (M : ℕ) : Convex ℝ (capsule M) :=
  (convex_segment _ _).cthickening _

lemma capsule_nonempty (M : ℕ) : (capsule M).Nonempty :=
  ⟨0, Metric.self_subset_cthickening _ (left_mem_segment _ _ _)⟩

lemma zero_mem_capsule (M : ℕ) : (0 : E3) ∈ capsule M :=
  Metric.self_subset_cthickening _ (left_mem_segment _ _ _)

lemma ctr_mem_capsule (M : ℕ) : ctr M ∈ capsule M :=
  Metric.self_subset_cthickening _ (right_mem_segment _ _ _)

lemma blob_subset_capsule {k M : ℕ} (h : k < M) : blob k ⊆ capsule M := by
  intro z hz
  refine Metric.mem_cthickening_of_dist_le z (ctr k) (1 / 16) _
    (Kakeya.ThinCase.Refute.ctr_mem_spine h.le) ?_
  linarith [dist_le_of_mem_blob hz]

lemma shadeSet_subset_capsule (M : ℕ) : shadeSet M ⊆ capsule M := by
  intro z hz
  obtain ⟨k, hk, hzk⟩ := Set.mem_iUnion₂.mp hz
  exact blob_subset_capsule (Finset.mem_range.mp hk) hzk

lemma closedBall_subset_capsule (M : ℕ) : Metric.closedBall (0 : E3) (1 / 16) ⊆ capsule M :=
  Metric.closedBall_subset_cthickening (left_mem_segment _ _ _) _

/-- Every point of the capsule is within `1/16` of an explicit point of the axis segment. -/
lemma exists_axis_point_of_mem_capsule {M : ℕ} {p : E3} (hp : p ∈ capsule M) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 2 * ((M : ℝ) + 1) ∧ dist p (t • axisVec) ≤ 1 / 16 := by
  have hcpt : IsCompact (spine M) := isCompact_segment
  rw [capsule, hcpt.cthickening_eq_biUnion_closedBall (by norm_num : (0 : ℝ) ≤ 1 / 16)] at hp
  obtain ⟨q, hq, hpq⟩ := Set.mem_iUnion₂.mp hp
  obtain ⟨u, v, hu, hv, huv, hquv⟩ := hq
  have hv1 : v ≤ 1 := by linarith
  have hMpos : (0 : ℝ) < 2 * ((M : ℝ) + 1) := by positivity
  refine ⟨v * (2 * ((M : ℝ) + 1)), by positivity, ?_, ?_⟩
  · nlinarith
  · have hqeq : (v * (2 * ((M : ℝ) + 1))) • axisVec = q := by
      rw [← smul_smul, ← ctr_eq_smul, ← hquv, smul_zero, zero_add]
    rw [hqeq]
    exact Metric.mem_closedBall.mp hpq

lemma capsule_subset_closedBall (M : ℕ) :
    capsule M ⊆ Metric.closedBall (0 : E3) (2 * ((M : ℝ) + 1) + 1 / 16) := by
  intro p hp
  obtain ⟨t, ht0, ht1, hd⟩ := exists_axis_point_of_mem_capsule hp
  rw [Metric.mem_closedBall]
  calc dist p 0 ≤ dist p (t • axisVec) + dist (t • axisVec) 0 := dist_triangle _ _ _
    _ ≤ 1 / 16 + t := by
        rw [dist_smul_axisVec_zero, abs_of_nonneg ht0]; linarith
    _ ≤ 2 * ((M : ℝ) + 1) + 1 / 16 := by linarith

/-! ### The thickness profile of the capsule -/

/-- The capsule lies in the `1/16`-neighbourhood of the axis line, hence has `n`-thickness at
most `1/16` for every `n ≥ 1`. -/
lemma thickness_capsule_le (M : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    Metric.thickness ℝ (capsule M) n ≤ 1 / 16 := by
  set R := { ε : ℝ | 0 ≤ ε ∧ ∃ A : AffineSubspace ℝ E3,
    Module.rank ℝ A.direction ≤ n ∧ capsule M ⊆ Metric.cthickening ε A } with hR
  have hbdd : BddBelow R := ⟨0, fun _ ↦ And.left⟩
  refine csInf_le hbdd ⟨by norm_num, ?_⟩
  refine ⟨(Submodule.span ℝ {axisVec}).toAffineSubspace, ?_, ?_⟩
  · rw [Submodule.toAffineSubspace_direction]
    refine le_trans (rank_span_le _) ?_
    rw [Cardinal.mk_singleton]
    exact_mod_cast hn
  · refine cthickening_subset_of_subset _ ?_
    have h0 : (0 : E3) ∈ ((Submodule.span ℝ {axisVec}).toAffineSubspace : Set E3) :=
      Submodule.zero_mem _
    have h1 : ctr M ∈ ((Submodule.span ℝ {axisVec}).toAffineSubspace : Set E3) := by
      change ctr M ∈ Submodule.span ℝ {axisVec}
      rw [ctr_eq_smul]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    exact (Submodule.span ℝ {axisVec}).convex.segment_subset h0 h1

lemma thickness_capsule_ge_two (M : ℕ) : (1 : ℝ) / 16 ≤ Metric.thickness ℝ (capsule M) 2 := by
  have h1 : Metric.thickness ℝ (Metric.closedBall (0 : E3) (1 / 16)) 2 ≤
      Metric.thickness ℝ (capsule M) 2 :=
    Metric.thickness_monotone (isCompact_capsule M).isBounded (closedBall_subset_capsule M) 2
  refine le_trans ?_ h1
  refine Metric.thickness_closedBall_ge (by norm_num) ?_
  rw [show Module.finrank ℝ E3 = 3 from finrank_euclideanSpace_fin]
  norm_num

lemma thickness_capsule_ge_one (M : ℕ) : (1 : ℝ) / 16 ≤ Metric.thickness ℝ (capsule M) 1 :=
  le_trans (thickness_capsule_ge_two M)
    (Metric.thickness_antitone (isCompact_capsule M).isBounded (by norm_num))

lemma thickness_capsule_zero_le (M : ℕ) :
    Metric.thickness ℝ (capsule M) 0 ≤ 2 * ((M : ℝ) + 1) + 1 / 16 :=
  Metric.thickness_le_of_subset_closedBall (capsule_subset_closedBall M) (by positivity) 0

lemma thickness_capsule_zero_ge (M : ℕ) :
    ((M : ℝ) + 1) ≤ Metric.thickness ℝ (capsule M) 0 := by
  have hd : dist (0 : E3) (ctr M) = 2 * ((M : ℝ) + 1) := by
    rw [dist_comm, ctr_eq_smul]
    have := dist_smul_axisVec_zero (2 * ((M : ℝ) + 1))
    rw [this, abs_of_nonneg (by positivity)]
  have h1 : ENNReal.ofReal (dist (0 : E3) (ctr M) / 2) ≤ Metric.ethickness ℝ (capsule M) 0 :=
    Metric.half_dist_le_ethickness_zero (zero_mem_capsule M) (ctr_mem_capsule M)
  rw [Metric.ethickness_thickness' (isCompact_capsule M).isBounded 0, hd] at h1
  have h2 := (ENNReal.ofReal_le_ofReal_iff (Metric.thickness_nonneg _ _)).mp h1
  linarith

/-- The thickness profile `(2(M+1), 1/8, 1/8)` with constant `2`. Both `IsBallFactoring.thick`
(at `(r₁, δ, δ)`) and `IsBallFactoring.body` (at `(r₁, b, a)`) are this one statement, because
the counterexample takes `δ = a = b = 1/8`. -/
lemma hasThicknesses_capsule (M : ℕ) :
    HasThicknesses (capsule M) 2 ![2 * ((M : ℝ) + 1), (1 / 8 : ℝ), (1 / 8 : ℝ)] := by
  intro k
  have hM : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  match k with
  | 0 =>
    refine ⟨?_, ?_⟩
    · have := thickness_capsule_zero_ge M
      simp only [Matrix.cons_val_zero, Fin.val_zero]
      push_cast
      linarith
    · have := thickness_capsule_zero_le M
      simp only [Matrix.cons_val_zero, Fin.val_zero]
      push_cast
      linarith
  | 1 =>
    refine ⟨?_, ?_⟩
    · have := thickness_capsule_ge_one M
      simp only [Matrix.cons_val_one, Fin.val_one]
      push_cast
      norm_num
      linarith
    · have := thickness_capsule_le M (n := 1) le_rfl
      simp only [Matrix.cons_val_one, Fin.val_one]
      push_cast
      norm_num
      linarith
  | 2 =>
    refine ⟨?_, ?_⟩
    · have := thickness_capsule_ge_two M
      simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
      push_cast
      norm_num
      linarith
    · have := thickness_capsule_le M (n := 2) (by norm_num)
      simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
      push_cast
      norm_num
      linarith

/-! ### The bodies -/

lemma volume_capsule_ne_top (M : ℕ) : volume (capsule M) ≠ ⊤ :=
  (isCompact_capsule M).measure_lt_top.ne

lemma volume_capsule_ne_zero (M : ℕ) : volume (capsule M) ≠ 0 := by
  refine ne_of_gt (lt_of_lt_of_le ?_ (measure_mono (closedBall_subset_capsule M)))
  exact measure_closedBall_pos _ _ (by norm_num)

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

/-! ### The `δ`-ball covers of (T5) -/

/-- The centre of the `j`-th covering ball: the point `j / 16` of the axis. -/
noncomputable def covCtr (j : ℕ) : E3 := ((j : ℝ) / 16) • axisVec

lemma dist_covCtr (j j' : ℕ) : dist (covCtr j) (covCtr j') = |(j : ℝ) / 16 - (j' : ℝ) / 16| :=
  dist_smul_axisVec _ _

lemma covCtr_mem_capsule {M j : ℕ} (h : j ≤ 32 * (M + 1)) : covCtr j ∈ capsule M := by
  refine Metric.self_subset_cthickening _ (smul_axisVec_mem_spine (by positivity) ?_)
  have hjR : (j : ℝ) ≤ 32 * ((M : ℝ) + 1) := by
    have : (j : ℝ) ≤ ((32 * (M + 1) : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at this
    linarith
  linarith

/-- The balls of radius `1/8` about the points `j / 16` of the axis, `0 ≤ j ≤ 32 (M+1)`, cover
the capsule: a point of the capsule is within `1/16` of the axis and within `1/32` of the
nearest such point, hence within `3/32 < 1/8`. -/
lemma capsule_subset_cover (M : ℕ) :
    capsule M ⊆ ⋃ j ∈ Finset.range (32 * (M + 1) + 1), Metric.ball (covCtr j) ((1 / 8 : ℝ)) := by
  intro p hp
  obtain ⟨t, ht0, ht1, hd⟩ := exists_axis_point_of_mem_capsule hp
  have hnn : (0 : ℝ) ≤ 16 * t + 1 / 2 := by linarith
  set j : ℕ := ⌊16 * t + 1 / 2⌋₊ with hj
  have hjle : (j : ℝ) ≤ 16 * t + 1 / 2 := Nat.floor_le hnn
  have hjgt : 16 * t + 1 / 2 < (j : ℝ) + 1 := Nat.lt_floor_add_one _
  have hjrange : j < 32 * (M + 1) + 1 := by
    rw [hj, Nat.floor_lt hnn]
    push_cast
    linarith
  refine Set.mem_iUnion₂.mpr ⟨j, Finset.mem_range.mpr hjrange, ?_⟩
  have hax : dist (t • axisVec) (covCtr j) = |t - (j : ℝ) / 16| := dist_smul_axisVec _ _
  have habs : |t - (j : ℝ) / 16| ≤ 1 / 32 := by
    rw [abs_le]
    constructor <;> linarith
  rw [Metric.mem_ball]
  calc dist p (covCtr j) ≤ dist p (t • axisVec) + dist (t • axisVec) (covCtr j) :=
        dist_triangle _ _ _
    _ ≤ 1 / 16 + 1 / 32 := by rw [hax]; linarith
    _ < 1 / 8 := by norm_num

open scoped Classical in
/-- The covering balls overlap at most `4`-fold: two of them meeting a common point have
centres within `1/4`, hence indices within `4`. -/
lemma cover_overlap (N : ℕ) (x : E3) :
    ((Finset.range N).filter (fun j => x ∈ Metric.ball (covCtr j) ((1 / 8 : ℝ)))).card ≤ 4 := by
  classical
  set S := (Finset.range N).filter (fun j => x ∈ Metric.ball (covCtr j) ((1 / 8 : ℝ))) with hS
  rcases S.eq_empty_or_nonempty with h | h
  · simp [h]
  · set m := S.min' h with hm
    have hmS : m ∈ S := S.min'_mem h
    have hclose : ∀ j ∈ S, j ≤ m + 3 := by
      intro j hj
      have hjx : dist x (covCtr j) < 1 / 8 :=
        Metric.mem_ball.mp (Finset.mem_filter.mp hj).2
      have hmx : dist x (covCtr m) < 1 / 8 :=
        Metric.mem_ball.mp (Finset.mem_filter.mp hmS).2
      have hdd : dist (covCtr j) (covCtr m) < 1 / 4 := by
        calc dist (covCtr j) (covCtr m) ≤ dist (covCtr j) x + dist x (covCtr m) :=
              dist_triangle _ _ _
          _ < 1 / 8 + 1 / 8 := by rw [dist_comm (covCtr j) x]; linarith
          _ = 1 / 4 := by norm_num
      rw [dist_covCtr] at hdd
      have hjm : m ≤ j := Finset.min'_le S j hj
      have hjmR : (m : ℝ) ≤ (j : ℝ) := by exact_mod_cast hjm
      have : (j : ℝ) - (m : ℝ) < 4 := by
        rw [abs_lt] at hdd
        linarith [hdd.2]
      have hlt : j < m + 4 := by
        by_contra hcon
        push Not at hcon
        have : ((m : ℝ) + 4) ≤ (j : ℝ) := by exact_mod_cast hcon
        linarith
      omega
    have hsub : S ⊆ Finset.Icc m (m + 3) := by
      intro j hj
      exact Finset.mem_Icc.mpr ⟨Finset.min'_le S j hj, hclose j hj⟩
    calc S.card ≤ (Finset.Icc m (m + 3)).card := Finset.card_le_card hsub
      _ = 4 := by rw [Nat.card_Icc]; omega

/-! ### The statement under test -/

/-- The statement of `Kakeya.ThinCase.perBall` **without the localisation hypothesis**, all
binders explicit, at `Type 0`. A universe-polymorphic statement is false as soon as one of its
instances is.

The declaration now carries one further hypothesis,
`hloc : ∃ z, ∀ j ∈ bodies, (Wb j).carrier ⊆ Metric.closedBall z 1`. That `hloc` is the *only*
difference is not a claim of the prose: `statement_of_universal_loc` below derives this exact
`Prop` from the current declaration by supplying `hloc` and nothing else, so it typechecks only
as long as that remains true. -/
def PerBallStatement : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E], Module.finrank ℝ E = 3 →
  ∀ {σ ω : Type} [DecidableEq ω] (segs : Finset σ) (Y : σ → ShadedBody E)
    (bodies : Finset ω) (Wb : ω → ConvexSpaceBody E) (blk : σ → ω)
    {δ a b r₁ w₁ : NNReal} {η : ℝ} {C₀ CF c₁ Ccore : NNReal} {D : ℕ},
    Kakeya.ThinCase.IsBallFactoring segs Y bodies Wb blk δ a b r₁ w₁ η C₀ CF c₁ →
    ∀ _bc : Kakeya.ThinCase.DeltaBallCovers.{0, 0, 0} segs Y δ D,
    δ ≤ w₁ → w₁ ≤ 1 → (0:ℝ) ≤ η → 2 ≤ Ccore →
    (ShadedBody.outerFactoringFamily_refinement.c 3 segs.card δ)⁻¹ ≤ Ccore →
    ShadedBody.outerFactoringFamily_outerConstMultFat.c 3 bodies.card δ ≤ Ccore →
    ((Nat.log 2 bodies.card + 1 : ℕ) : NNReal) ≤ Ccore →
    ((Nat.log 2 ⌈CF⌉₊ + 1 : ℕ) : NNReal) ≤ Ccore →
    (ShadedBody.outerFactoringFamily_refinement.c 3 segs.card (δ / C₀))⁻¹ ≤ Ccore →
    ShadedBody.outerFactoringFamily_outerConstMultFat.c 3 bodies.card (δ / C₀) ≤ Ccore →
    Kakeya.ThinCase.thinEnvelopeTerm 3 segs.card bodies.card CF w₁ ≤ Ccore →
    Nonempty (Kakeya.ThinCase.ThinBall
      (Kakeya.ThinCase.perBallConstant C₀ CF c₁ Ccore D) C₀ segs Y bodies Wb blk δ a η)

/-- **Tripwire / fidelity check.** Granting the localisation hypothesis universally and for
free, the current `Kakeya.ThinCase.perBall` *is* `PerBallStatement`: the `IsBallFactoring`
bundle, the `DeltaBallCovers` bundle and every scalar hypothesis — including the two
scale-dependent envelope bounds at `δ / C₀` that the discretization repair added, which the
counterexample supplies rather than being granted — are passed through verbatim. So `hloc` is
the only hypothesis granted rather than supplied, and the refutation below still bites on
everything else.

`hLoc` is of course false — `not_subset_closedBall_one` exhibits a body violating it — so
combining this with `perBall_refuted` merely reproves `¬ hLoc`, which is sound. -/
theorem statement_of_universal_loc
    (hLoc : ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {ω : Type}
      (bodies : Finset ω) (Wb : ω → ConvexSpaceBody E),
      ∃ z : E, ∀ j ∈ bodies, (Wb j).carrier ⊆ Metric.closedBall z 1) :
    PerBallStatement := by
  intro E instE₁ instE₂ instE₃ instE₄ instE₅ hdim σ ω instω segs Y bodies Wb blk
    δ a b r₁ w₁ η C₀ CF c₁ Ccore D hfac bc hδw₁ hw₁one hη hCcore2 hCcoreRef hCcoreMult hCcoreDyad
    hCcoreFrost hCcoreRef₀ hCcoreMult₀ hCcoreNet
  exact Kakeya.ThinCase.perBall hdim segs Y bodies Wb blk hfac bc hδw₁ hw₁one hη
    (hLoc bodies Wb)
    hCcore2 hCcoreRef hCcoreMult hCcoreDyad hCcoreFrost hCcoreRef₀ hCcoreMult₀ hCcoreNet

/-! ### Parameter choices -/

lemma exists_eta {q : ENNReal} (hq0 : q ≠ 0) (hqt : q ≠ ⊤) :
    ∃ n : ℕ, ((1 / 8 : NNReal) : ENNReal) ^ ((n : ℕ) : ℝ) ≤ q := by
  lift q to NNReal using hqt with f
  have hf : f ≠ 0 := by simpa using hq0
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < (f : ℝ) by positivity)
    (show (1 / 8 : ℝ) < 1 by norm_num)
  refine ⟨n, ?_⟩
  rw [ENNReal.rpow_natCast, ← ENNReal.coe_pow]
  refine ENNReal.coe_le_coe.mpr ?_
  rw [← NNReal.coe_le_coe]
  push_cast
  linarith

/-- The density hypothesis (C5) at the configuration: some natural exponent works. -/
lemma exists_dens (M : ℕ) (hM : 0 < M) :
    ∃ n : ℕ, ((1 : NNReal) : ENNReal) * ((1 / 8 : NNReal) : ENNReal) ^ ((n : ℕ) : ℝ) *
      volume (capsule M) ≤ volume (shadeSet M) := by
  have hcap0 : volume (capsule M) ≠ 0 := volume_capsule_ne_zero M
  have hcapt : volume (capsule M) ≠ ⊤ := volume_capsule_ne_top M
  set q : ENNReal := volume (shadeSet M) / volume (capsule M) with hq
  have hq0 : q ≠ 0 := by
    rw [hq, Ne, ENNReal.div_eq_zero_iff]
    push Not
    exact ⟨(volume_shadeSet_pos hM).ne', hcapt⟩
  have hqt : q ≠ ⊤ := by
    rw [hq]
    exact ENNReal.div_ne_top (ne_top_of_le_ne_top hcapt
      (measure_mono (shadeSet_subset_capsule M))) hcap0
  obtain ⟨n, hn⟩ := exists_eta hq0 hqt
  refine ⟨n, ?_⟩
  rw [show ((1 : NNReal) : ENNReal) = 1 from by simp, one_mul]
  calc ((1 / 8 : NNReal) : ENNReal) ^ ((n : ℕ) : ℝ) * volume (capsule M)
      ≤ q * volume (capsule M) := by gcongr
    _ = volume (shadeSet M) := by
        rw [hq]
        exact ENNReal.div_mul_cancel hcap0 hcapt

/-! ### The refutation -/

/-- **`Kakeya.ThinCase.perBall` is false as stated.**

The `ThinBall` it produces carries the same unachievable pair of clauses that refutes
`Kakeya.ThinCase.factoringApply`: the centred multiplicity comparison at the *equal* radius
`A = rad C₀ a`, and the termwise refinement on the non-empty subfamily `𝒮_B`. With one segment
in one body the constant `perBallConstant C₀ CF c₁ Ccore D` is one fixed number, while the
harmonic configuration forces `∑_{k<M} (k+1)⁻¹ ≤ C ^ 2` for every `M`. -/
theorem perBall_refuted : ¬ PerBallStatement := by
  classical
  intro H
  -- the core envelope is now read at *two* scales: `δ = 1/8`, for the four `δ`-bounds, and
  -- `δ / C₀ = (1/8)/2`, the scale at which `IsBallFactoring.thick` discretizes the segment, for
  -- the two scale-dependent bounds the repair added. Both are fixed numbers, independent of `M`.
  set Cc : NNReal := max
    (max (factoringApplyCore 3 1 1 (1 / 8 : NNReal))
      (factoringApplyCore 3 1 1 ((1 / 8 : NNReal) / 2)))
    (Kakeya.ThinCase.thinEnvelopeTerm 3 1 1 1 (1 / 8 : NNReal)) with hCcdef
  set C : NNReal := perBallConstant 2 1 1 Cc 4 with hCdef
  obtain ⟨M, hM⟩ := exists_harmonic_gt ((C : ℝ) ^ 2)
  have hMpos : 0 < M := by
    rcases Nat.eq_zero_or_pos M with h | h
    · exfalso; rw [h] at hM; simp at hM; nlinarith [hM, sq_nonneg (C : ℝ)]
    · exact h
  obtain ⟨n, hn⟩ := exists_dens M hMpos
  have hdim : Module.finrank ℝ E3 = 3 := finrank_euclideanSpace_fin
  have hthick2 : Module.finrank ℝ E3 - 1 = 2 := by rw [hdim]
  have hcard : (Finset.univ : Finset Unit).card = 1 := by simp
  obtain ⟨hc2, hcref, hcmult, hcdyad⟩ := factoringApplyCore_spec 3 1 1 (1 / 8 : NNReal)
  obtain ⟨-, hcref₀, hcmult₀, -⟩ := factoringApplyCore_spec 3 1 1 ((1 / 8 : NNReal) / 2)
  -- the ball factoring data
  have hfac : Kakeya.ThinCase.IsBallFactoring (E := E3) (Finset.univ : Finset Unit)
      (fun _ => shadedBody M) (Finset.univ : Finset Unit) (fun _ => carrierBody M)
      (fun _ => ()) (1 / 8 : NNReal) (1 / 8 : NNReal) (1 / 8 : NNReal)
      ((2 * (M + 1) : ℕ) : NNReal) (1 / 8 : NNReal) ((n : ℕ) : ℝ) 2 1 1 := by
    refine
      { one_le_C₀ := by norm_num
        one_le_CF := le_rfl
        c₁_pos := by norm_num
        δ_pos := by norm_num
        δ_le_a := le_rfl
        a_le_b := le_rfl
        b_le_r₁ := ?_
        segs_nonempty := ⟨(), Finset.mem_univ _⟩
        blk_mem := fun _ _ => Finset.mem_univ _
        le_block := fun _ _ => le_rfl
        thick := ?_
        dims := ?_
        body := ?_
        width := ?_
        frostman := ?_
        dens := ?_ }
    · -- `b ≤ r₁`
      rw [← NNReal.coe_le_coe]
      push_cast
      have : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
      norm_num
      linarith
    · -- `thick`
      intro p _
      have h := hasThicknesses_capsule M
      have hr : (((2 * (M + 1) : ℕ) : NNReal) : ℝ) = 2 * ((M : ℝ) + 1) := by push_cast; ring
      have hd : (((1 / 8 : NNReal)) : ℝ) = (1 / 8 : ℝ) := by norm_num
      change HasThicknesses ((shadedBody M).carrier) 2 _
      rw [hr, hd]
      exact h
    · -- `dims`
      intro p _ q _ i
      simp only [Pi.smul_apply, nsmul_eq_mul, Nat.cast_ofNat]
      nlinarith [Metric.thickness_nonneg (𝕜 := ℝ) ((shadedBody M).carrier) i]
    · -- `body`
      intro j _
      have h := hasThicknesses_capsule M
      have hr : (((2 * (M + 1) : ℕ) : NNReal) : ℝ) = 2 * ((M : ℝ) + 1) := by push_cast; ring
      have hd : (((1 / 8 : NNReal)) : ℝ) = (1 / 8 : ℝ) := by norm_num
      change HasThicknesses ((carrierBody M).carrier) 2 _
      rw [hr, hd]
      exact h
    · -- `width`
      intro j _
      rw [hthick2]
      refine ⟨?_, ?_⟩
      · change Metric.thickness ℝ (capsule M) 2 ≤ 2 * (((1 / 8 : NNReal)) : ℝ)
        have := thickness_capsule_le M (n := 2) (by norm_num)
        push_cast
        linarith
      · change (((1 / 8 : NNReal)) : ℝ) ≤ 2 * Metric.thickness ℝ (capsule M) 2
        have := thickness_capsule_ge_two M
        push_cast
        linarith
    · -- `frostman`
      intro j _
      have hfil : (Finset.univ.filter (fun _ : Unit => (() : Unit) = j)) = Finset.univ := by
        ext p; simp
      rw [hfil]
      exact Kakeya.ThinCase.Refute.isFrostmanIn_self (volume_capsule_ne_zero M)
        (volume_capsule_ne_top M)
    · -- `dens`
      intro p _
      exact hn
  -- the `δ`-ball covers
  have hbc : Kakeya.ThinCase.DeltaBallCovers.{0, 0, 0} (E := E3) (Finset.univ : Finset Unit)
      (fun _ => shadedBody M) (1 / 8 : NNReal) 4 :=
    { γ := ℕ
      cov := fun _ => Finset.range (32 * (M + 1) + 1)
      ctr := covCtr
      one_le_D := by norm_num
      isCover := by
        intro p _
        refine ⟨?_, ?_⟩
        · have hcov := capsule_subset_cover M
          have hd : (((1 / 8 : NNReal)) : ℝ) = (1 / 8 : ℝ) := by norm_num
          simpa [hd] using hcov
        · intro x
          have hd : (((1 / 8 : NNReal)) : ℝ) = (1 / 8 : ℝ) := by norm_num
          simpa [hd] using cover_overlap (32 * (M + 1) + 1) x
      meets := by
        intro p _ i hi
        refine ⟨covCtr i, ?_, ?_⟩
        · exact Metric.mem_ball_self (by norm_num)
        · exact covCtr_mem_capsule (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) }
  obtain ⟨tb⟩ := H (E := E3) hdim (Finset.univ : Finset Unit) (fun _ => shadedBody M)
    (Finset.univ : Finset Unit) (fun _ => carrierBody M) (fun _ => ()) (Ccore := Cc)
    hfac hbc le_rfl (by rw [← NNReal.coe_le_coe]; norm_num) (Nat.cast_nonneg n)
    ((hc2.trans (le_max_left _ _)).trans (le_max_left _ _))
    (by rw [hcard]; exact (hcref.trans (le_max_left _ _)).trans (le_max_left _ _))
    (by rw [hcard]; exact (hcmult.trans (le_max_left _ _)).trans (le_max_left _ _))
    (by rw [hcard]; exact (hcdyad.trans (le_max_left _ _)).trans (le_max_left _ _))
    (le_trans (by norm_num) ((hc2.trans (le_max_left _ _)).trans (le_max_left _ _)))
    (by rw [hcard]; exact (hcref₀.trans (le_max_right _ _)).trans (le_max_left _ _))
    (by rw [hcard]; exact (hcmult₀.trans (le_max_right _ _)).trans (le_max_left _ _))
    (le_max_right _ _)
  -- the produced constant is `C`
  have hCne : C ≠ 0 := by
    rw [hCdef]
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one one_le_perBallConstant)
  have hCneE : (C : ENNReal) ≠ 0 := by simpa using hCne
  have hCtop : (C : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  -- the radius of `ThinBall.centredMult` is `rad 2 (1/8) = 1`
  have hrad : ((Kakeya.ThinCase.rad 2 (1 / 8 : NNReal) : NNReal) : ℝ) = 1 := by
    norm_num [Kakeya.ThinCase.rad, Kakeya.ThinCase.w1Constant]
  -- the retained shading
  set U' : Set E3 := (tb.Y' ()).shade with hU'
  have hUnion : ShadedBody.iUnionShade (Finset.univ : Finset Unit) tb.Y' = U' := by
    ext z
    simp only [ShadedBody.iUnionShade, Set.mem_iUnion, Finset.mem_univ, exists_prop,
      true_and, hU']
    exact ⟨fun ⟨i, hi⟩ => by cases i; exact hi, fun h => ⟨(), h⟩⟩
  have hsub : U' ⊆ shadeSet M := by
    have := tb.shade_Y'_subset () (Finset.mem_univ _)
    simpa [hU'] using this
  -- clause (vi): the termwise refinement on the non-empty `𝒮_B`
  have hvi : (C : ENNReal)⁻¹ * volume (shadeSet M) ≤ volume U' := by
    obtain ⟨p, hp⟩ := tb.S_nonempty
    have hp' : (() : Unit) ∈ tb.S := by cases p; exact hp
    have h1 := tb.refine_S () hp'
    simp only [shadedBody_shade] at h1
    exact (ENNReal.inv_mul_le_iff hCneE hCtop).mpr (by rw [hCdef]; exact h1)
  -- clause (iv): the centred multiplicity comparison at radius `A = 1`
  have hiv : ∀ x ∈ U', ∀ y ∈ U',
      volume (U' ∩ Metric.ball x 1) ≤ (C : ENNReal) * volume (U' ∩ Metric.ball y 1) := by
    intro x hx y hy
    have hxU : x ∈ ShadedBody.iUnionShade (Finset.univ : Finset Unit) tb.Y' := by
      rw [hUnion]; exact hx
    have hyU : y ∈ ShadedBody.iUnionShade (Finset.univ : Finset Unit) tb.Y' := by
      rw [hUnion]; exact hy
    have h := tb.centredMult x hxU y hyU
    rwa [hUnion, hrad, ← hCdef] at h
  have := harmonic_le_of_centredMult M C hCne (tb.Y' ()).measurableSet_shade hsub hiv hvi
  linarith

/-! ### Which hypothesis the configuration violates -/

/-- **The localisation the counterexample violates.**

The witness body has diameter `≥ 2(M+1)`, so for `M ≥ 1` it lies in **no** ball of radius `1`,
whatever the centre. This is `ConvexSpaceBody.IsDiscretizedAtScale.subset_unitBall` — the
hypothesis every item of GWZ Proposition 5.1 assumes and `Kakeya.ThinCase.factoringApply` drops
— read at `Kakeya.ThinCase.IsBallFactoring`, which does not have it either.

The call site *can* supply it: `Kakeya.VeryNotSticky.BallData.bodies_subset_ball` says
`(Wb j).carrier ⊆ closedBall (ctr B) r₁` with `r₁ = δ ^ exscal ≤ 1` (from
`VeryNotSticky.hδ1` and `VeryNotSticky.hexscal`). So the repair is a genuine one and not a
hypothesis nobody can discharge. -/
theorem not_subset_closedBall_one {M : ℕ} (hM : 1 ≤ M) (z : E3) :
    ¬ ((carrierBody M).carrier ⊆ Metric.closedBall z 1) := by
  intro h
  have h0 : (0 : E3) ∈ Metric.closedBall z 1 := h (zero_mem_capsule M)
  have hM' : ctr M ∈ Metric.closedBall z 1 := h (ctr_mem_capsule M)
  have hd : dist (0 : E3) (ctr M) ≤ 2 := by
    refine le_trans (dist_triangle (0 : E3) z (ctr M)) ?_
    have h1 := Metric.mem_closedBall.mp h0
    have h2 := Metric.mem_closedBall.mp hM'
    rw [dist_comm z (ctr M)]
    linarith
  have hdd : dist (0 : E3) (ctr M) = 2 * ((M : ℝ) + 1) := by
    rw [dist_comm, ctr_eq_smul]
    rw [dist_smul_axisVec_zero, abs_of_nonneg (by positivity)]
  rw [hdd] at hd
  have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  linarith

end Kakeya.ThinCase.PerBallRefute

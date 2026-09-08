/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineDescentSite
public import Kakeya.DimensionThree.MainLemma2.VeryNotStickyClosed
public import Kakeya.DimensionThree.MainLemma2.AxialEDObstruction
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSiteClosure

/-!
# Non-vacuity witnesses: the site hypothesis and GWZ Lemma 9.1's binder list

`Kakeya.ML2Core.geometricCoreAt_of_site`, `Kakeya.ML2Core.geometricCoreAt_of_descent` and
`Kakeya.ML2Cap.mainLemma2Statement_of_geometricCoreAt_free` are all axiom-clean, so a **vacuously
discharged** `hsite` would prove Main Lemma 2 from nothing while `check`, `scan`, `axioms` and
`guard` all stayed green.  This leaf supplies the control that no mechanical gate can: a family for which every clause of the hypothesis list actually holds.

## What is proved

* `Kakeya.ML2Wit.exists_siteRows_nonvacuity` — **W1.**  There is a `Cu₀` such that for every
  `ε > 0` there is a `δ < ε` and a concrete `(s, T)` in universe `v` meeting the four input
  clauses of `hsite` (`Kakeya.ML2Wit.SiteInputs`) **and** its whole conclusion row list
  (`Kakeya.ML2Wit.SiteRows`) — the retained `u' ⊆ s`, the hierarchy at the hoisted `Cu₀`, the
  mass ledger, `Kakeya.ML2Core.IsTrialAtGain` and all four absorptions included.  So `hsite` is
  not vacuously true on any tail of `𝓝[>] 0`.
* `Kakeya.ML2Wit.exists_siteWitness_nonvacuity` — **W1′, the closing skeleton's shape.**  The row
  block of `Kakeya.ML2Core.SiteWitness` (the *downward* re-cut: four data existentials, ten rows, no
  `ε₀'`/`g'`) is inhabited at arbitrarily small `δ`, at the same absolute `Cu₀` and — the
  measurement that matters — with **`K = 1`**.  Taking `u' := s` (the ambient family already *is*
  the retained one) and `lam := 1` makes the mass ledger an identity, because
  `Kakeya.ML2Core.stateMass` ignores the shading level, so the outer margin row
  `K · δ^(dm − aL) ≤ 1` reduces to `aL ≤ dm` and the `α ≤ dm − aL ≤ β/48000` cap is met with room
  to spare.  `Kakeya.ML2Wit.SiteWitnessRows`'s body is  to
  `Reduction/SpineSiteClosure.lean:94–106` (`md5sum` `7d60514f620cf7749c36c4ece442b83a`; the
  surrounding `:87–106` pins at `19559d0d5eb7ebd9d9db4b35d9050900`), which is the tie until that
  file is in the tree and the `example : SiteWitnessPred → ML2Core.SiteWitness := id` compatibility can
  be written.
* `Kakeya.ML2Wit.SiteHypothesis` and the `example` beside it are a **compatibility**: the row list is
  spelled out here and handed to `Kakeya.ML2Core.geometricCoreAt_of_site`, so a drift between this
  file's transcription and the tree's stops elaboration rather than passing silently.  Measured
  firing control: perturbing one row (`Cu ≤ Cu₀` to `Cu ≤ Cu₀ + 1`) makes the `example` fail.
* `Kakeya.ML2Wit.exists_lemma91BindersNoCount_nonvacuity` — **W2.**  Five of GWZ Lemma 9.1's six
  binders — ball, **centredness**, `1 ≤ C ≤ δ^{-η}` uniformity, `Δ_max ≤ δ^{-η}`, `λ ≥ δ^{η}` —
  hold simultaneously on a family that is *not* axially degenerate (its carriers are pairwise
  disjoint and it has more than `δ^{-1}` members), at arbitrarily small `δ`.  This is the point
  `Kakeya.VeryNotSticky.exists_witnessFamily` cannot make: its family is a set of axial translates
  of one tube, which the centredness binder excludes.  `Kakeya.ML2Wit.lemma91_of_binders` is the
  compatibility: GWZ Lemma 9.1 restated through the two `def`s, so a transcription weaker than the
  tree's does not elaborate (firing control: replacing the centredness clause by `True` breaks it).
* `Kakeya.ML2Wit.lemma91Binders_vacuous_of_exponents` — **the sixth binder is the one that is not
  jointly satisfiable.**  If `(1-ϖ)(2+ζ) > 2 + η` then at every small `δ` *no* family meets both
  the five binders and the `ρ`-count, so GWZ Lemma 9.1 is vacuously true at those exponents.  Two
  bounds meet: `#𝕋_ρ ≤ 2 · 385^6 · #𝕋` (`Kakeya.ML2Wit.card_used_le`, from
  `Kakeya.VeryNotSticky.card_le_of_ed_of_endpoints_confined`) and `#𝕋 ≤ C₃ δ^{-2-η}`
  (`Kakeya.ML2Wit.card_le_of_maxDensity`), against `#𝕋_ρ ≥ ρ^{-2-ζ} = δ^{-(1-ϖ)(2+ζ)}` at the
  window's fine end `ρ = δ^{1-ϖ}`.  The usable tolerance range is `ζ ≤ (η + 2ϖ)/(1-ϖ)`, and
  `Kakeya.ML2Wit.vacuity_range_nonempty` records that the excluded range is not empty.

## The family

`Kakeya.ML2Wit.wcore` is an `M × M` grid of parallel `δ`-tubes at `δ = 1/(24 M)`, spaced `3 δ`
apart in the two transverse coordinates and centred on the third axis.  Three properties do all
the work:

* the carriers are **pairwise disjoint** (`Kakeya.ML2Wit.wcarrier_disjoint`), which gives
  `Δ_max ≤ 1` (`Kakeya.ML2Wit.maxDensity_le_one_of_disjoint`) — the *only* route to a density
  bound below `δ^{-η}` for a family of more than `δ^{-1}` tubes, since
  `Kakeya.maxDensity_le_card` never gets below the cardinality;
* they are **centred** in the sense of `Kakeya.Tube.IsCentred` (`Kakeya.ML2Wit.wcore_isCentred`):
  the core's midpoint is orthogonal to its direction;
* the family is **uniform at an absolute constant** after passing to the retained subfamily of
  `Kakeya.ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf`, which costs `δ^{-1/2}` of the
  cardinality and leaves `≥ δ^{-1}` members.  The shading is then re-set to the whole carrier, so
  no fullness is lost; the hierarchy is untouched because it only reads the tubes.

**Scope.**  A non-vacuity witness says the hypothesis list is inhabited; it does not say the
site's *intended* families satisfy it.  The trial `Kakeya.ML2Core.IsTrialAtGain` is met here
through its sticky exit, which for a disjoint family is an identity
(`∑ |Y_i| = |⋃ Y_i|`), and the loss is `Λ = 1`.
-/

@[expose] public section

open MeasureTheory Metric ConvexSpaceBody ShadedBody
open scoped NNReal ENNReal

namespace Kakeya.ML2Wit

open Kakeya.VeryNotSticky.Produce (E3)

/-! ## Generic: a pairwise disjoint family has maximal density at most one -/

theorem maxDensity_le_one_of_disjoint {ι : Type*} {s : Finset ι} (W : ι → ConvexSpaceBody E3)
    (hdisj : (s : Set ι).Pairwise fun i j => Disjoint (W i).carrier (W j).carrier) :
    Kakeya.maxDensity s W ≤ 1 := by
  classical
  refine Kakeya.maxDensity_le_of_forall_sum_le (fun K => ?_)
  set t : Finset ι := {i ∈ s | W i ≤ K} with ht
  have hts : t ⊆ s := Finset.filter_subset _ _
  have hmeas : ∀ i ∈ t, MeasurableSet (W i).carrier :=
    fun i _ => (W i).isCompact.measurableSet
  have hpd : (t : Set ι).PairwiseDisjoint fun i => (W i).carrier := by
    intro i hi j hj hij
    exact hdisj (hts hi) (hts hj) hij
  have hsum : ∑ i ∈ t, volume (W i).carrier = volume (⋃ i ∈ t, (W i).carrier) :=
    (measure_biUnion_finset hpd hmeas).symm
  rw [one_mul, hsum]
  refine measure_mono (Set.iUnion₂_subset fun i hi => ?_)
  exact SetLike.coe_subset_coe.mpr (Finset.mem_filter.mp hi).2

theorem sum_volume_shade_eq_of_disjoint {ι : Type*} {s : Finset ι} (V : ι → ShadedBody E3)
    (hdisj : (s : Set ι).Pairwise fun i j => Disjoint (V i).shade (V j).shade) :
    ∑ i ∈ s, volume (V i).shade = volume (⋃ i ∈ s, (V i).shade) :=
  (measure_biUnion_finset (fun i hi j hj hij => hdisj hi hj hij)
    (fun i _ => (V i).measurableSet_shade)).symm

/-! ## The grid family -/

noncomputable def ax (k : Fin 3) : E3 := EuclideanSpace.single k (1 : ℝ)

theorem norm_ax (k : Fin 3) : ‖ax k‖ = 1 := by simp [ax]

theorem ax_apply (k j : Fin 3) : ax k j = if j = k then (1:ℝ) else 0 := by simp [ax]

/-- The scale attached to the grid parameter `M`: `δ = 1 / (24 M)`. -/
noncomputable def wδ (M : ℕ) : NNReal := ((24 * M : NNReal))⁻¹

theorem wδ_coe (M : ℕ) : ((wδ M : NNReal) : ℝ) = (24 * (M:ℝ))⁻¹ := by
  simp [wδ]

theorem wδ_pos {M : ℕ} (hM : 1 ≤ M) : 0 < wδ M := by
  have hMr : (1:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM
  have : (0:ℝ) < ((wδ M : NNReal) : ℝ) := by rw [wδ_coe]; positivity
  exact_mod_cast this

theorem wδ_lt_one {M : ℕ} (hM : 1 ≤ M) : wδ M < 1 := by
  have hMr : (1:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM
  have : ((wδ M : NNReal) : ℝ) < 1 := by
    rw [wδ_coe, inv_lt_one₀ (by positivity)]
    linarith
  exact_mod_cast this

theorem three_wδ_mul (M : ℕ) (hM : 1 ≤ M) : 3 * ((wδ M : NNReal):ℝ) * (M:ℝ) = 8⁻¹ := by
  have hMr : (0:ℝ) < (M:ℝ) := by
    have : (1:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM
    linarith
  rw [wδ_coe]
  field_simp
  ring

noncomputable def wbase (M : ℕ) (p : Fin M × Fin M) : E3 :=
  (3 * (wδ M : ℝ) * (p.1 : ℝ)) • ax 0 + (3 * (wδ M : ℝ) * (p.2 : ℝ)) • ax 1
    - (2⁻¹ : ℝ) • ax 2

theorem wbase_apply0 (M : ℕ) (p : Fin M × Fin M) :
    wbase M p 0 = 3 * (wδ M : ℝ) * (p.1 : ℝ) := by simp [wbase, ax_apply]

theorem wbase_apply1 (M : ℕ) (p : Fin M × Fin M) :
    wbase M p 1 = 3 * (wδ M : ℝ) * (p.2 : ℝ) := by simp [wbase, ax_apply]

theorem wdist (M : ℕ) (p : Fin M × Fin M) : dist (wbase M p) (wbase M p + ax 2) = 1 := by
  rw [dist_eq_norm]
  have h : wbase M p - (wbase M p + ax 2) = -(ax 2) := by abel
  rw [h, norm_neg, norm_ax]

/-- The `p`-th grid tube: a `δ`-tube of unit length parallel to the third axis. -/
noncomputable def wcore (M : ℕ) (p : Fin M × Fin M) : Tube (wδ M) E3 :=
  Tube.mk' (wδ M) (wdist M p)

theorem wcore_x (M : ℕ) (p : Fin M × Fin M) : (wcore M p).x = wbase M p := rfl
theorem wcore_y (M : ℕ) (p : Fin M × Fin M) : (wcore M p).y = wbase M p + ax 2 := rfl

theorem wseg_apply (M : ℕ) (p : Fin M × Fin M) {z : E3}
    (hz : z ∈ segment ℝ (wcore M p).x (wcore M p).y) :
    z 0 = 3 * (wδ M : ℝ) * (p.1 : ℝ) ∧ z 1 = 3 * (wδ M : ℝ) * (p.2 : ℝ) := by
  rw [segment_eq_image'] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  have hxy : (wcore M p).y - (wcore M p).x = ax 2 := by rw [wcore_x, wcore_y]; abel
  rw [hxy]
  refine ⟨?_, ?_⟩
  · have h : ((wcore M p).x + t • ax 2) 0 = (wcore M p).x 0 + t * (ax 2 0) := rfl
    rw [h, wcore_x, wbase_apply0, ax_apply]
    norm_num [show (0 : Fin 3) ≠ 2 by decide]
  · have h : ((wcore M p).x + t • ax 2) 1 = (wcore M p).x 1 + t * (ax 2 1) := rfl
    rw [h, wcore_x, wbase_apply1, ax_apply]
    norm_num [show (1 : Fin 3) ≠ 2 by decide]

theorem norm_wseg_le {M : ℕ} (hM : 1 ≤ M) (p : Fin M × Fin M) {z : E3}
    (hz : z ∈ segment ℝ (wcore M p).x (wcore M p).y) : ‖z‖ ≤ 4⁻¹ + 2⁻¹ := by
  have hMr : (0:ℝ) < (M:ℝ) := by
    have : (1:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM
    linarith
  have hδ0 : (0:ℝ) < ((wδ M : NNReal) : ℝ) := by rw [wδ_coe]; positivity
  rw [segment_eq_image'] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  have hxy : (wcore M p).y - (wcore M p).x = ax 2 := by rw [wcore_x, wcore_y]; abel
  rw [hxy, wcore_x]
  show ‖wbase M p + t • ax 2‖ ≤ 4⁻¹ + 2⁻¹
  have hsplit : wbase M p + t • ax 2
      = ((3 * (wδ M : ℝ) * (p.1 : ℝ)) • ax 0 + (3 * (wδ M : ℝ) * (p.2 : ℝ)) • ax 1)
        + (t - 2⁻¹) • ax 2 := by
    rw [wbase, sub_smul]; module
  rw [hsplit]
  have h1 : ‖(3 * (wδ M : ℝ) * (p.1 : ℝ)) • ax 0 + (3 * (wδ M : ℝ) * (p.2 : ℝ)) • ax 1‖
      ≤ 3 * (wδ M : ℝ) * (p.1 : ℝ) + 3 * (wδ M : ℝ) * (p.2 : ℝ) := by
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_smul, norm_smul, norm_ax, norm_ax, mul_one, mul_one, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  have h2 : ‖(t - 2⁻¹) • ax 2‖ ≤ 2⁻¹ := by
    rw [norm_smul, norm_ax, mul_one, Real.norm_eq_abs, abs_le]
    obtain ⟨ht0, ht1⟩ := ht
    constructor <;> linarith
  have hkey : ∀ a : Fin M, 3 * ((wδ M : NNReal):ℝ) * (a : ℝ) ≤ 8⁻¹ := by
    intro a
    have hale : ((a : ℕ) : ℝ) ≤ (M:ℝ) := by exact_mod_cast a.isLt.le
    have h0 : (0:ℝ) ≤ 3 * ((wδ M : NNReal):ℝ) := by linarith
    have := three_wδ_mul M hM
    nlinarith
  have := norm_add_le ((3 * (wδ M : ℝ) * (p.1 : ℝ)) • ax 0
    + (3 * (wδ M : ℝ) * (p.2 : ℝ)) • ax 1) ((t - 2⁻¹) • ax 2)
  have ha := hkey p.1
  have hb := hkey p.2
  linarith

theorem wcarrier_subset_ball {M : ℕ} (hM : 1 ≤ M) (p : Fin M × Fin M) :
    (wcore M p).carrier ⊆ Metric.closedBall (0 : E3) 1 := by
  have hMr : (1:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM
  intro w hw
  rw [(wcore M p).carrier_eq] at hw
  obtain ⟨z, hz, hwz⟩ := Set.mem_iUnion₂.1 hw
  have hzn : ‖z‖ ≤ 4⁻¹ + 2⁻¹ := norm_wseg_le hM p hz
  have hd : dist w z ≤ ((wδ M : NNReal) : ℝ) := Metric.mem_closedBall.1 hwz
  have hδle : ((wδ M : NNReal) : ℝ) ≤ 24⁻¹ := by
    rw [wδ_coe, inv_le_inv₀ (by positivity) (by norm_num)]
    linarith
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  have hwn : ‖w‖ ≤ ‖z‖ + dist w z := by
    rw [dist_eq_norm]
    calc ‖w‖ = ‖z + (w - z)‖ := by rw [add_sub_cancel]
      _ ≤ ‖z‖ + ‖w - z‖ := norm_add_le _ _
  linarith

theorem wcarrier_disjoint {M : ℕ} (hM : 1 ≤ M) {p q : Fin M × Fin M} (hpq : p ≠ q) :
    Disjoint (wcore M p).carrier (wcore M q).carrier := by
  have hMr : (0:ℝ) < (M:ℝ) := by
    have : (1:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM
    linarith
  have hδ0 : (0:ℝ) < ((wδ M : NNReal) : ℝ) := by rw [wδ_coe]; positivity
  rw [Set.disjoint_left]
  intro w hwp hwq
  rw [(wcore M p).carrier_eq] at hwp
  rw [(wcore M q).carrier_eq] at hwq
  obtain ⟨zp, hzp, hwp'⟩ := Set.mem_iUnion₂.1 hwp
  obtain ⟨zq, hzq, hwq'⟩ := Set.mem_iUnion₂.1 hwq
  have hdp : dist w zp ≤ ((wδ M : NNReal) : ℝ) := Metric.mem_closedBall.1 hwp'
  have hdq : dist w zq ≤ ((wδ M : NNReal) : ℝ) := Metric.mem_closedBall.1 hwq'
  have hpq2 : dist zp zq ≤ 2 * ((wδ M : NNReal) : ℝ) := by
    have h := dist_triangle zp w zq
    rw [dist_comm zp w] at h
    linarith
  obtain ⟨hzp0, hzp1⟩ := wseg_apply M p hzp
  obtain ⟨hzq0, hzq1⟩ := wseg_apply M q hzq
  have hcoord : ∀ j : Fin 3, |zp j - zq j| ≤ 2 * ((wδ M : NNReal) : ℝ) := by
    intro j
    have h := PiLp.dist_apply_le zp zq j
    rw [Real.dist_eq] at h
    linarith
  have key : ∀ (a b : Fin M), 3 * ((wδ M : NNReal) : ℝ) * (a : ℝ)
      - 3 * ((wδ M : NNReal) : ℝ) * (b : ℝ) ≤ 2 * ((wδ M : NNReal) : ℝ) →
      -(2 * ((wδ M : NNReal) : ℝ)) ≤ 3 * ((wδ M : NNReal) : ℝ) * (a : ℝ)
        - 3 * ((wδ M : NNReal) : ℝ) * (b : ℝ) → a = b := by
    intro a b h1 h2
    by_contra hne
    have hab : ((a : ℕ) : ℝ) ≠ ((b : ℕ) : ℝ) := fun h => hne (Fin.ext (by exact_mod_cast h))
    rcases lt_or_gt_of_ne hab with h | h
    · have hge : ((b : ℕ) : ℝ) - ((a : ℕ) : ℝ) ≥ 1 := by
        have : ((a : ℕ) : ℝ) + 1 ≤ ((b : ℕ) : ℝ) := by
          exact_mod_cast Nat.succ_le_of_lt (by exact_mod_cast h)
        linarith
      nlinarith
    · have hge : ((a : ℕ) : ℝ) - ((b : ℕ) : ℝ) ≥ 1 := by
        have : ((b : ℕ) : ℝ) + 1 ≤ ((a : ℕ) : ℝ) := by
          exact_mod_cast Nat.succ_le_of_lt (by exact_mod_cast h)
        linarith
      nlinarith
  have h0 := hcoord 0
  have h1 := hcoord 1
  rw [hzp0, hzq0, abs_le] at h0
  rw [hzp1, hzq1, abs_le] at h1
  exact hpq (Prod.ext (key p.1 q.1 h0.2 h0.1) (key p.2 q.2 h1.2 h1.1))


/-! ## The fully shaded grid family, indexed in an arbitrary universe -/

universe v

/-- The fully shaded grid tube. -/
noncomputable def wshaded (M : ℕ) (p : Fin M × Fin M) : ShadedTube (wδ M) E3 where
  toTube := wcore M p
  shade := (wcore M p).carrier
  measurableSet_shade := (wcore M p).toConvexSpaceBody.isCompact.measurableSet
  shade_subset := subset_rfl

/-- The grid family, indexed in universe `v`. -/
noncomputable def wfam (M : ℕ) (i : ULift.{v} (Fin M × Fin M)) : ShadedTube (wδ M) E3 :=
  wshaded M i.down

theorem wfam_carrier (M : ℕ) (i : ULift.{v} (Fin M × Fin M)) :
    (wfam M i).carrier = (wcore M i.down).carrier := rfl

theorem wfam_ball {M : ℕ} (hM : 1 ≤ M) (i : ULift.{v} (Fin M × Fin M)) :
    (wfam M i).carrier ⊆ Metric.closedBall (0 : E3) 1 :=
  wcarrier_subset_ball hM i.down

theorem wfam_disjoint {M : ℕ} (hM : 1 ≤ M) {i j : ULift.{v} (Fin M × Fin M)} (hij : i ≠ j) :
    Disjoint (wfam M i).carrier (wfam M j).carrier := by
  refine wcarrier_disjoint hM (fun h => hij ?_)
  cases i; cases j; simpa using h

theorem card_wfam_univ (M : ℕ) :
    (Finset.univ : Finset (ULift.{v} (Fin M × Fin M))).card = M * M := by
  simp


theorem wδ_rpow_neg {M : ℕ} (hM : 1 ≤ M) (r : ℝ) :
    ((wδ M : NNReal):ℝ) ^ (-r) = (24*(M:ℝ))^r := by
  have hMr : (0:ℝ) < (M:ℝ) := by
    have : (1:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM
    linarith
  have h24 : (0:ℝ) < 24*(M:ℝ) := by positivity
  rw [wδ_coe, Real.inv_rpow h24.le, Real.rpow_neg h24.le, inv_inv]

theorem one_le_rpow_neg_of_le_one {δ : NNReal} (hδ1 : δ ≤ 1) {x : ℝ} (hx : 0 ≤ x) :
    (1:ℝ≥0∞) ≤ (δ : ℝ≥0∞) ^ (-x) := by
  have h1 : (δ : ℝ≥0∞) ≤ 1 := by exact_mod_cast hδ1
  have h := ENNReal.rpow_le_rpow_of_exponent_ge h1 (show -x ≤ (0:ℝ) by linarith)
  simpa using h

theorem wδ_inv {M : ℕ} (hM : 1 ≤ M) : ((wδ M : NNReal):ℝ)⁻¹ = 24*(M:ℝ) := by
  rw [wδ_coe, inv_inv]

theorem wδ_rpow_half {M : ℕ} (hM : 1 ≤ M) :
    ((wδ M : NNReal):ℝ) ^ (-(1/2:ℝ)) * ((wδ M : NNReal):ℝ) ^ (-(1/2:ℝ)) = 24*(M:ℝ) := by
  have hMr : (0:ℝ) < (M:ℝ) := by
    have : (1:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM
    linarith
  have hδr : (0:ℝ) < ((wδ M : NNReal):ℝ) := by rw [wδ_coe]; positivity
  rw [← Real.rpow_add hδr]
  norm_num
  rw [Real.rpow_neg_one, wδ_inv hM]

theorem wδ_rpow_neg_one {M : ℕ} (hM : 1 ≤ M) :
    ((wδ M : NNReal):ℝ) ^ (-(1:ℝ)) = 24*(M:ℝ) := by
  rw [wδ_rpow_neg hM, Real.rpow_one]

/-! ## Generic consequences of disjointness -/

theorem tube_carrier_congr {δ : NNReal} {A B : ShadedTube δ E3} (h : A.toTube = B.toTube) :
    A.carrier = B.carrier := congrArg (fun t : Tube δ E3 => t.carrier) h

theorem fullness_eq_one_of_fullShade {ι : Type*} {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {s : Finset ι} (T : ι → ShadedTube δ E3) (hsh : ∀ i ∈ s, (T i).shade = (T i).carrier)
    (hne : s.Nonempty) : ShadedBody.fullness s (fun i => (T i).toShadedBody) = 1 := by
  obtain ⟨i₀, hi₀⟩ := hne
  have hpos : ∀ i, 0 < volume (T i).carrier :=
    fun i => (Tube.volume_pos_and_lt_top hδ0 hδ1 (T i).toTube).1
  have hfin : ∀ i, volume (T i).carrier < ⊤ :=
    fun i => (Tube.volume_pos_and_lt_top hδ0 hδ1 (T i).toTube).2
  have hne0 : (∑ i ∈ s, volume (T i).carrier) ≠ 0 := by
    refine ne_of_gt (lt_of_lt_of_le (hpos i₀) ?_)
    exact Finset.single_le_sum (f := fun i => volume (T i).carrier)
      (fun i _ => by positivity) hi₀
  have htop : (∑ i ∈ s, volume (T i).carrier) ≠ ⊤ :=
    (ENNReal.sum_lt_top.mpr (fun i _ => hfin i)).ne
  have h1 : ((ShadedBody.fullness s (fun i => (T i).toShadedBody) : NNReal) : ENNReal) = 1 := by
    rw [ShadedBody.fullness_def, Finset.sum_congr rfl (fun i hi => by
      exact congrArg volume (hsh i hi))]
    exact ENNReal.div_self hne0 htop
  exact_mod_cast h1

theorem trialAtGain_of_disjoint {ι : Type*} {δ Cu : NNReal} {u : Finset ι}
    {T : ι → ShadedTube δ E3}
    (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
    (hdisj : (u : Set ι).Pairwise fun i j => Disjoint (T i).carrier (T j).carrier)
    (g β h ηin : ℝ) (Λ : ℝ≥0∞) :
    ML2Core.IsTrialAtGain 0 g β h ηin 𝒰 Λ := by
  intro S hS Z lam _ hZtube hZshade _ _ _ _ _ _ _
  left
  have hZcar : ∀ i, (Z i).carrier = (T i).carrier := fun i => tube_carrier_congr (hZtube i)
  have hsub : ∀ i, (Z i).shade ⊆ (T i).carrier := by
    intro i x hx
    exact (hZcar i) ▸ (Z i).shade_subset hx
  have hd : (S : Set ι).Pairwise fun i j => Disjoint (Z i).shade (Z j).shade := by
    intro i hi j hj hij
    exact Set.disjoint_of_subset (hsub i) (hsub j) (hdisj (hS hi) (hS hj) hij)
  have hsum : ∑ i ∈ S, volume (Z i).shade = volume (⋃ i ∈ S, (Z i).shade) :=
    sum_volume_shade_eq_of_disjoint (fun i => (Z i).toShadedBody) hd
  rw [hsum]
  simp

/-! ## The row list of `hsite`, named -/

/-- The four input clauses of `Kakeya.ML2Core.geometricCoreAt_of_site`'s `hsite`. -/
def SiteInputs (η : ℝ) {δ : NNReal} {ι : Type v} (s : Finset ι) (T : ι → ShadedTube δ E3) :
    Prop :=
  (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) ∧
  IsKatzTao s (fun i => (T i).toConvexSpaceBody) ((δ : ℝ≥0∞) ^ (-η)) ∧
  ShadedBody.fullness s (fun i => (T i).toShadedBody) ≥ δ ^ η ∧
  (δ : ℝ)⁻¹ ≤ (s.card : ℝ)

/-- The conclusion row list of `Kakeya.ML2Core.geometricCoreAt_of_site`'s `hsite`, verbatim
(the C1 shape: the hierarchy sits on a **retained** `u' ⊆ s`, and the chain's mass ledger and its
two outer absorptions stand beside the descent's). -/
def SiteRows (β ϖ ε₁ : ℝ) (gain dens : ℝ → ℝ) (Cu₀ : NNReal) {δ : NNReal} {ι : Type v}
    (s : Finset ι) (T : ι → ShadedTube δ E3) : Prop :=
  ∃ u' : Finset ι, u' ⊆ s ∧
  ∃ (Cu : NNReal) (𝒰 : Tube.UniformTubeSet u' (fun i => (T i).toTube)
      (Tube.ssfGridLen δ) Cu) (lam : NNReal) (Λ K : ℝ≥0∞)
      (ε₀ g ε₀' g' ηin h α : ℝ),
    Cu ≤ Cu₀ ∧
    0 < δ ∧ δ < 1 ∧ 0 < h ∧ 1 ≤ Λ ∧ Λ ≠ ⊤ ∧
    (u'.card : ℝ) ≤ (δ : ℝ) ^ (-(4 : ℝ)) ∧
    (Cu : ℝ) ≤ (δ : ℝ) ^ (-(1 : ℝ)) ∧
    u'.Nonempty ∧
    Kakeya.maxDensity u' (fun i => (T i).toConvexSpaceBody) ≤ (δ : ℝ≥0∞) ^ (-ηin) ∧
    0 < lam ∧
    ML2Shaded.HasDenseShading lam u' (fun i => (T i).toShadedBody) ∧
    (Λ ^ ML2Core.potentialCeil h 5 δ * (((δ : NNReal) ^ ηin / 2 : NNReal) : ℝ≥0∞)
      ≤ (((δ : NNReal) ^ (ηin - α) / 2 : NNReal) : ℝ≥0∞)) ∧
    ((((δ : NNReal) ^ (ηin - α) / 2 : NNReal) : ℝ≥0∞) ≤ (lam : ℝ≥0∞)) ∧
    ML2Core.IsTrialAtGain ε₀ g β h ηin 𝒰 Λ ∧
    (Λ ^ ML2Core.potentialCeil h 5 δ * (δ : ℝ≥0∞) ^ (-ε₀) ≤ (δ : ℝ≥0∞) ^ (-ε₀')) ∧
    (Λ ^ ML2Core.potentialCeil h 5 δ * (δ : ℝ≥0∞) ^ g ≤ (δ : ℝ≥0∞) ^ g') ∧
    ML2Core.stateMass ((s, T, (1 : NNReal)) : ML2Core.DescentState ι δ)
      ≤ K * ML2Core.stateMass ((u', T, lam) : ML2Core.DescentState ι δ) ∧
    (K * (δ : ℝ≥0∞) ^ (-ε₀') ≤ (δ : ℝ≥0∞) ^ (-(β / 2))) ∧
    (K * (δ : ℝ≥0∞) ^ g'
      ≤ (δ : ℝ≥0∞) ^ (4 * ML2Spine.spineNu β ϖ ε₁ gain dens))

/-- `hsite` itself. -/
def SiteHypothesis : Prop :=
  ∀ (β ϖ : ℝ) (gain dens : ℝ → ℝ), 0 < β → β ≤ 1 →
    ML2Assembly.Lemma91ParamsAt.{v} β ϖ gain dens →
    KatzTaoEstimate.{v} (EuclideanSpace ℝ (Fin 3)) β →
    FrostmanEstimate.{v} (EuclideanSpace ℝ (Fin 3)) β →
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∃ Cu₀ : NNReal,
      ∀ᶠ (δ : NNReal) in nhdsWithin 0 (Set.Ioi 0),
        ∀ {ι : Type v} (s : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
          (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
          IsKatzTao s (fun i => (T i).toConvexSpaceBody) ((δ : ℝ≥0∞) ^ (-η)) →
          ShadedBody.fullness s (fun i => (T i).toShadedBody) ≥ δ ^ η →
          (δ : ℝ)⁻¹ ≤ (s.card : ℝ) →
          SiteRows.{v} β ϖ ε₁ gain dens Cu₀ s T

/-- **compatibility.**  `SiteHypothesis` is *the* hypothesis of the existing
`Kakeya.ML2Core.geometricCoreAt_of_site`; if the row list above ever drifts from the tree's, this
`example` stops elaborating. -/
example : SiteHypothesis.{v} → ML2Assembly.GeometricCoreAt.{v} :=
  ML2Core.geometricCoreAt_of_site

/-! ## Centredness -/

/-- The grid tubes are **centred**: the midpoint of the core is orthogonal to its direction. -/
theorem wcore_isCentred (M : ℕ) (p : Fin M × Fin M) : (wcore M p).IsCentred := by
  have hmid : (wcore M p).midpoint
      = (3 * (wδ M : ℝ) * (p.1 : ℝ)) • ax 0 + (3 * (wδ M : ℝ) * (p.2 : ℝ)) • ax 1 := by
    show (1/2 : ℝ) • ((wcore M p).x + (wcore M p).y) = _
    rw [wcore_x, wcore_y, wbase]
    module
  have hdir : (wcore M p).direction = ax 2 := by
    show (wcore M p).y - (wcore M p).x = ax 2
    rw [wcore_x, wcore_y]; abel
  show inner ℝ (wcore M p).midpoint (wcore M p).direction = (0:ℝ)
  rw [hmid, hdir]
  simp [ax, PiLp.inner_apply]

/-! ## The packaged witness family -/

/-- The full shading of a shaded tube: same tube, shade the whole carrier. -/
noncomputable def fullShade {δ : NNReal} (Z : ShadedTube δ E3) : ShadedTube δ E3 where
  toTube := Z.toTube
  shade := (Z.toTube).carrier
  measurableSet_shade := (Z.toTube).toConvexSpaceBody.isCompact.measurableSet
  shade_subset := subset_rfl

theorem wδ_lt_of_inv_lt {M : ℕ} {ε : ℝ} (hM : 1 ≤ M) (hε : 0 < ε) (h : ε⁻¹ < (M:ℝ)) :
    ((wδ M : NNReal):ℝ) < ε := by
  have hMr : (1:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM
  rw [wδ_coe, inv_lt_iff_one_lt_mul₀ (by positivity)]
  rw [inv_lt_iff_one_lt_mul₀ hε] at h
  nlinarith

/-- **The construction.**  Beyond any threshold `A` there is a grid parameter `M` whose family,
after the uniformisation of `Kakeya.ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf`, retains
at least `δ^{-1} = 24 M` of its `M²` members and carries GWZ Definition 2.2 at the **absolute**
constant `Kakeya.ShadedTube.ssfUniformConst 3`. -/
theorem exists_gridWitness (a : ℝ) (ha : 0 < a) (A : ℝ) :
    ∃ (M : ℕ) (s' : Finset (ULift.{v} (Fin M × Fin M)))
      (V' : ULift.{v} (Fin M × Fin M) → ShadedTube (wδ M) E3),
      1 ≤ M ∧ A < (M:ℝ) ∧
      (∀ i, (V' i).toTube = (wfam M i).toTube) ∧
      s' ⊆ Finset.univ ∧ s'.Nonempty ∧
      (M:ℝ) * (M:ℝ) ≤ ((wδ M : NNReal):ℝ) ^ (-a) * (s'.card : ℝ) ∧
      Nonempty (ShadedTube.ShadedUniformTubeSet s' V' (Tube.ssfGridLen (wδ M))
        (ShadedTube.ssfUniformConst (Module.finrank ℝ E3))) := by
  classical
  obtain ⟨δ₀, hδ₀pos, hδ₀le1, hprod⟩ :=
    ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf.{v} (E := E3) 2 a 1
      ha (by norm_num)
  have hδ₀r : (0:ℝ) < (δ₀:ℝ) := by exact_mod_cast hδ₀pos
  obtain ⟨M, hMgt⟩ := exists_nat_gt (max ((δ₀:ℝ)⁻¹) (max 13824 A))
  have hMδ₀ : (δ₀:ℝ)⁻¹ < (M:ℝ) := lt_of_le_of_lt (le_max_left _ _) hMgt
  have hMbig : (13824:ℝ) < (M:ℝ) :=
    lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hMgt
  have hMA : A < (M:ℝ) := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hMgt
  have hM1 : 1 ≤ M := by
    rcases Nat.eq_zero_or_pos M with rfl | h
    · norm_num at hMbig
    · exact h
  have hMr : (1:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM1
  have hMpos : (0:ℝ) < (M:ℝ) := by linarith
  have hδpos : 0 < wδ M := wδ_pos hM1
  have hδr : (0:ℝ) < ((wδ M : NNReal):ℝ) := by rw [wδ_coe]; positivity
  have hδδ₀ : wδ M ≤ δ₀ := by
    have h : ((wδ M : NNReal):ℝ) ≤ (δ₀:ℝ) := by
      rw [wδ_coe, inv_le_comm₀ (by positivity) hδ₀r]
      linarith
    exact_mod_cast h
  have hcarduniv : ((Finset.univ : Finset (ULift.{v} (Fin M × Fin M))).card : ℝ)
      = (M:ℝ) * (M:ℝ) := by simp [Finset.card_univ]
  have hball0 : ∀ i ∈ (Finset.univ : Finset (ULift.{v} (Fin M × Fin M))),
      (wfam M i).carrier ⊆ Metric.closedBall (0 : E3) 1 := fun i _ => wfam_ball hM1 i
  have hsq2 : ((24:ℝ)*(M:ℝ))^(2:ℝ) = (24*(M:ℝ))*(24*(M:ℝ)) := by
    rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]; ring
  have hcard0 : ((Finset.univ : Finset (ULift.{v} (Fin M × Fin M))).card : ℝ)
      ≤ ((wδ M : NNReal):ℝ) ^ (-((2:ℕ) : ℝ)) := by
    rw [hcarduniv, show (-((2:ℕ):ℝ)) = -(2:ℝ) by norm_num, wδ_rpow_neg hM1, hsq2]
    nlinarith
  obtain ⟨s', hs'sub, V', hV'tube, hV'shade, hcard', -, hU⟩ :=
    hprod (ι := ULift.{v} (Fin M × Fin M)) hδpos hδδ₀ Finset.univ (wfam M) hball0 hcard0
  rw [hcarduniv] at hcard'
  have hu0 : (0:ℝ) < ((wδ M : NNReal):ℝ) ^ (-a) := Real.rpow_pos_of_pos hδr _
  have hs'ne : s'.Nonempty := by
    rw [← Finset.card_pos]
    have h : (0:ℝ) < (s'.card : ℝ) := by nlinarith
    exact_mod_cast h
  exact ⟨M, s', V', hM1, hMA, hV'tube, hs'sub, hs'ne, hcard', hU⟩

/-- `Kakeya.ML2Wit.exists_gridWitness` at the uniformisation exponent `1/2`, where the retained
subfamily still has more than `δ^{-1}` members. -/
theorem exists_gridWitness_half (A : ℝ) :
    ∃ (M : ℕ) (s' : Finset (ULift.{v} (Fin M × Fin M)))
      (V' : ULift.{v} (Fin M × Fin M) → ShadedTube (wδ M) E3),
      1 ≤ M ∧ A < (M:ℝ) ∧
      (∀ i, (V' i).toTube = (wfam M i).toTube) ∧
      s' ⊆ Finset.univ ∧ s'.Nonempty ∧
      24 * (M:ℝ) ≤ (s'.card : ℝ) ∧
      Nonempty (ShadedTube.ShadedUniformTubeSet s' V' (Tube.ssfGridLen (wδ M))
        (ShadedTube.ssfUniformConst (Module.finrank ℝ E3))) := by
  obtain ⟨M, s', V', hM1, hMA, hV'tube, hs'sub, hs'ne, hcard', hU⟩ :=
    exists_gridWitness.{v} (1/2) (by norm_num) (max A 13824)
  have hMA' : A < (M:ℝ) := lt_of_le_of_lt (le_max_left _ _) hMA
  have hMbig : (13824:ℝ) < (M:ℝ) := lt_of_le_of_lt (le_max_right _ _) hMA
  have hMr : (1:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM1
  have hMpos : (0:ℝ) < (M:ℝ) := by linarith
  have hδr : (0:ℝ) < ((wδ M : NNReal):ℝ) := by rw [wδ_coe]; positivity
  refine ⟨M, s', V', hM1, hMA', hV'tube, hs'sub, hs'ne, ?_, hU⟩
  have hu0 : (0:ℝ) < ((wδ M : NNReal):ℝ) ^ (-(1/2:ℝ)) := Real.rpow_pos_of_pos hδr _
  have hu2 : ((wδ M : NNReal):ℝ) ^ (-(1/2:ℝ)) * ((wδ M : NNReal):ℝ) ^ (-(1/2:ℝ))
      = 24*(M:ℝ) := wδ_rpow_half hM1
  have hMsq : 24*(M:ℝ) < ((M:ℝ)/24) * ((M:ℝ)/24) := by nlinarith
  have hule : ((wδ M : NNReal):ℝ) ^ (-(1/2:ℝ)) ≤ (M:ℝ)/24 := by
    by_contra hcon
    push_neg at hcon
    have h1 : ((M:ℝ)/24) * ((M:ℝ)/24)
        ≤ ((wδ M : NNReal):ℝ) ^ (-(1/2:ℝ)) * ((wδ M : NNReal):ℝ) ^ (-(1/2:ℝ)) :=
      mul_le_mul hcon.le hcon.le (by positivity) hu0.le
    rw [hu2] at h1
    linarith
  have hc0 : (0:ℝ) ≤ (s'.card : ℝ) := Nat.cast_nonneg _
  have h2 : (M:ℝ)*(M:ℝ) ≤ ((M:ℝ)/24) * (s'.card:ℝ) :=
    le_trans hcard' (mul_le_mul_of_nonneg_right hule hc0)
  have h3 : (M:ℝ) * (24 * (M:ℝ)) ≤ (M:ℝ) * (s'.card:ℝ) := by nlinarith
  exact le_of_mul_le_mul_left h3 hMpos

/-! ## W1 — the site's row list is inhabited

The input family is the whole `M × M` grid; the retained `u'` is what the uniformisation of
`Kakeya.ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf` keeps, at the absolute constant
`Kakeya.ShadedTube.ssfUniformConst 3`.  The uniformisation is run at the exponent `β/4`, which is
what the chain's outer absorption `K · δ^{-ε₀'} ≤ δ^{-β/2}` can pay for: the ledger constant `K`
is the uniformisation's own cardinality loss `δ^{-β/4}`, and the terminal exponent is opened by
the same `β/4` (`g' = 4·spineNu + β/4`), which the second outer absorption then closes. -/

theorem exists_siteRows_nonvacuity :
    ∃ Cu₀ : NNReal,
      ∀ (β ϖ ε₁ η : ℝ) (gain dens : ℝ → ℝ), 0 < β → 0 ≤ η → ∀ ε : ℝ, 0 < ε →
        ∃ δ : NNReal, 0 < δ ∧ (δ : ℝ) < ε ∧
          ∃ (ι : Type v) (s : Finset ι) (T : ι → ShadedTube δ E3),
            SiteInputs.{v} η s T ∧ SiteRows.{v} β ϖ ε₁ gain dens Cu₀ s T := by
  classical
  refine ⟨ShadedTube.ssfUniformConst (Module.finrank ℝ E3), ?_⟩
  intro β ϖ ε₁ η gain dens hβ0 hη0 ε hε
  obtain ⟨M, s', V', hM1, hMA, hV'tube, hs'sub, hs'ne, hcard', ⟨𝒮⟩⟩ :=
    exists_gridWitness.{v} (β/4) (by linarith)
      (max (max (ε⁻¹) ((ShadedTube.ssfUniformConst (Module.finrank ℝ E3) : NNReal) : ℝ)) 24)
  have hMε : ε⁻¹ < (M:ℝ) :=
    lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hMA
  have hMcu : ((ShadedTube.ssfUniformConst (Module.finrank ℝ E3) : NNReal) : ℝ) < (M:ℝ) :=
    lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hMA
  have hM24 : (24:ℝ) < (M:ℝ) := lt_of_le_of_lt (le_max_right _ _) hMA
  have hMr : (1:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM1
  have hMpos : (0:ℝ) < (M:ℝ) := by linarith
  have hM0 : 0 < M := hM1
  have hδpos : 0 < wδ M := wδ_pos hM1
  have hδlt1 : wδ M < 1 := wδ_lt_one hM1
  have hδle1 : wδ M ≤ 1 := le_of_lt hδlt1
  have hδr : (0:ℝ) < ((wδ M : NNReal):ℝ) := by rw [wδ_coe]; positivity
  have hne : (wδ M : NNReal) ≠ 0 := hδpos.ne'
  have hδE0 : ((wδ M : NNReal) : ℝ≥0∞) ≠ 0 := by simpa using hne
  have hδE1 : ((wδ M : NNReal) : ℝ≥0∞) ≤ 1 := by exact_mod_cast hδle1
  refine ⟨wδ M, hδpos, wδ_lt_of_inv_lt hM1 hε hMε, ?_⟩
  have hFcar : ∀ i, (fullShade (V' i)).carrier = (wfam M i).carrier := fun i =>
    congrArg (fun t : Tube (wδ M) E3 => t.carrier) (hV'tube i)
  have hFshade : ∀ i, (fullShade (V' i)).shade = (fullShade (V' i)).carrier := fun _ => rfl
  have hFdisj : ∀ (t : Finset (ULift.{v} (Fin M × Fin M))),
      ((t : Finset (ULift.{v} (Fin M × Fin M))) : Set (ULift.{v} (Fin M × Fin M))).Pairwise
        fun i j => Disjoint (fullShade (V' i)).carrier (fullShade (V' j)).carrier := by
    intro t i _ j _ hij
    rw [hFcar i, hFcar j]
    exact wfam_disjoint hM1 hij
  have hFmax : ∀ (t : Finset (ULift.{v} (Fin M × Fin M))),
      Kakeya.maxDensity t (fun i => (fullShade (V' i)).toConvexSpaceBody) ≤ 1 := fun t =>
    maxDensity_le_one_of_disjoint (fun i => (fullShade (V' i)).toConvexSpaceBody) (hFdisj t)
  have hcarduniv : ((Finset.univ : Finset (ULift.{v} (Fin M × Fin M))).card : ℝ)
      = (M:ℝ) * (M:ℝ) := by simp [Finset.card_univ]
  have hi₀ : (⟨(⟨0, hM0⟩, ⟨0, hM0⟩)⟩ : ULift.{v} (Fin M × Fin M)) ∈
      (Finset.univ : Finset (ULift.{v} (Fin M × Fin M))) := Finset.mem_univ _
  have hFfull : ShadedBody.fullness (Finset.univ : Finset (ULift.{v} (Fin M × Fin M)))
      (fun i => (fullShade (V' i)).toShadedBody) = 1 :=
    fullness_eq_one_of_fullShade hδpos hδle1 (fun i => fullShade (V' i))
      (fun i _ => hFshade i) ⟨_, hi₀⟩
  -- the mass ledger: equal volumes, so the ratio is the cardinality ratio
  set w : ℝ≥0∞ :=
    volume (fullShade (V' (⟨(⟨0, hM0⟩, ⟨0, hM0⟩)⟩ : ULift.{v} (Fin M × Fin M)))).shade with hwdef
  have hsum : ∀ t : Finset (ULift.{v} (Fin M × Fin M)),
      ∑ i ∈ t, volume (fullShade (V' i)).shade = (t.card : ℝ≥0∞) * w := by
    intro t
    have hvol : ∀ i ∈ t, volume (fullShade (V' i)).shade = w := by
      intro i _
      rw [hwdef]
      exact _root_.Tube.volume_carrier_eq_volume_carrier _ _
    rw [Finset.sum_congr rfl hvol, Finset.sum_const, nsmul_eq_mul]
  have hcastN : ((Finset.univ : Finset (ULift.{v} (Fin M × Fin M))).card : NNReal)
      ≤ (wδ M) ^ (-(β/4)) * ((s'.card : ℕ) : NNReal) := by
    rw [← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_rpow]
    simp only [NNReal.coe_natCast]
    rw [hcarduniv]
    exact hcard'
  have hcastE : ((Finset.univ : Finset (ULift.{v} (Fin M × Fin M))).card : ℝ≥0∞)
      ≤ ((wδ M : NNReal) : ℝ≥0∞) ^ (-(β/4)) * ((s'.card : ℕ) : ℝ≥0∞) := by
    rw [← ENNReal.coe_rpow_of_ne_zero hne,
      show (((Finset.univ : Finset (ULift.{v} (Fin M × Fin M))).card : ℕ) : ℝ≥0∞)
        = (((Finset.univ : Finset (ULift.{v} (Fin M × Fin M))).card : NNReal) : ℝ≥0∞) by simp,
      show ((s'.card : ℕ) : ℝ≥0∞) = ((s'.card : NNReal) : ℝ≥0∞) by simp,
      ← ENNReal.coe_mul, ENNReal.coe_le_coe]
    exact hcastN
  refine ⟨ULift.{v} (Fin M × Fin M), Finset.univ, fun i => fullShade (V' i),
    ⟨?_, ?_, ?_, ?_⟩, s', hs'sub,
    ShadedTube.ssfUniformConst (Module.finrank ℝ E3), 𝒮.tubeUniform, 1, 1,
    ((wδ M : NNReal) : ℝ≥0∞) ^ (-(β/4)),
    0, 4 * ML2Spine.spineNu β ϖ ε₁ gain dens + β/4,
    0, 4 * ML2Spine.spineNu β ϖ ε₁ gain dens + β/4, 0, 1, 0,
    le_rfl, hδpos, hδlt1, one_pos, le_rfl, ENNReal.one_ne_top, ?_, ?_, hs'ne, ?_, one_pos,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- ball
    intro i _
    rw [hFcar i]
    exact wfam_ball hM1 i
  · -- Katz–Tao
    exact le_trans (hFmax _) (one_le_rpow_neg_of_le_one hδle1 hη0)
  · -- fullness
    rw [hFfull]
    exact NNReal.rpow_le_one hδle1 hη0
  · -- `δ⁻¹ ≤ #s`
    rw [wδ_inv hM1, hcarduniv]
    nlinarith
  · -- `#u' ≤ δ^{-4}`
    rw [wδ_rpow_neg hM1]
    have h4 : ((24:ℝ)*(M:ℝ))^(4:ℝ)
        = ((24*(M:ℝ))*(24*(M:ℝ)))*((24*(M:ℝ))*(24*(M:ℝ))) := by
      rw [show (4:ℝ) = ((4:ℕ):ℝ) by norm_num, Real.rpow_natCast]; ring
    have hsle : (s'.card : ℝ) ≤ (M:ℝ)*(M:ℝ) := by
      have h := Finset.card_le_card hs'sub
      have h' : ((s'.card : ℕ) : ℝ)
          ≤ ((Finset.univ : Finset (ULift.{v} (Fin M × Fin M))).card : ℝ) := by exact_mod_cast h
      rw [hcarduniv] at h'
      exact h'
    rw [h4]
    have hA : (1:ℝ) ≤ 24*(M:ℝ) := by linarith
    have h1 : (M:ℝ)*(M:ℝ) ≤ (24*(M:ℝ))*(24*(M:ℝ)) := by nlinarith
    have hX : (1:ℝ) ≤ (24*(M:ℝ))*(24*(M:ℝ)) := by nlinarith
    have h2 : (24*(M:ℝ))*(24*(M:ℝ))
        ≤ ((24*(M:ℝ))*(24*(M:ℝ)))*((24*(M:ℝ))*(24*(M:ℝ))) := by nlinarith
    linarith
  · -- `Cu ≤ δ^{-1}`
    rw [wδ_rpow_neg_one hM1]
    linarith
  · -- density on the retained family
    simpa using hFmax s'
  · -- dense shading
    intro i _
    refine le_of_eq ?_
    rw [ENNReal.coe_one, one_mul]
    rfl
  · simp
  · simp
  · exact trialAtGain_of_disjoint (T := fun i => fullShade (V' i)) 𝒮.tubeUniform (hFdisj s')
      _ _ _ _ _
  · simp
  · simp
  · -- the mass ledger
    show ∑ i ∈ (Finset.univ : Finset (ULift.{v} (Fin M × Fin M))),
        volume (fullShade (V' i)).shade
      ≤ ((wδ M : NNReal) : ℝ≥0∞) ^ (-(β/4))
        * ∑ i ∈ s', volume (fullShade (V' i)).shade
    rw [hsum Finset.univ, hsum s', ← mul_assoc]
    exact mul_le_mul_right' hcastE w
  · -- the first outer absorption
    have h : ((wδ M : NNReal) : ℝ≥0∞) ^ (-(β/4))
        ≤ ((wδ M : NNReal) : ℝ≥0∞) ^ (-(β/2)) :=
      ENNReal.rpow_le_rpow_of_exponent_ge hδE1 (by linarith)
    simpa using h
  · -- the second outer absorption
    have hadd : ((wδ M : NNReal) : ℝ≥0∞) ^ (-(β/4))
        * ((wδ M : NNReal) : ℝ≥0∞) ^ (4 * ML2Spine.spineNu β ϖ ε₁ gain dens + β/4)
        = ((wδ M : NNReal) : ℝ≥0∞) ^ (4 * ML2Spine.spineNu β ϖ ε₁ gain dens) := by
      rw [← ENNReal.rpow_add _ _ hδE0 ENNReal.coe_ne_top]
      ring_nf
    rw [hadd]

/-! ## W2 — GWZ Lemma 9.1's binder list, minus the `ρ`-count

`Kakeya.VeryNotSticky.exists_witnessFamily` inhabits the *pre-centred* binder list with a family of
axial translates of one tube — a family whose members all lie inside the union of two of them, and
which `Kakeya.Tube.IsCentred` excludes (centred tubes on a common supporting line coincide).  The
witness below is the opposite extreme: pairwise **disjoint** carriers, all centred, and more than
`δ^{-1}` of them, so the axial refutation does not transfer to it. -/

/-- For a family whose **shades** are pairwise disjoint, GWZ Definition 2.2 costs nothing beyond
Definition 2.1: every shade class is a singleton, so both class brackets and both branching
brackets hold with the constant of the tube hierarchy. -/
theorem nonempty_shadedUniformTubeSet_of_disjoint {ι : Type*} {δ Cu : NNReal} {s : Finset ι}
    {T : ι → ShadedTube δ E3}
    (𝒰 : Tube.UniformTubeSet s (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
    (hCu : 1 ≤ Cu)
    (hdisj : (s : Set ι).Pairwise fun i j => Disjoint (T i).shade (T j).shade) :
    Nonempty (ShadedTube.ShadedUniformTubeSet s T (Tube.ssfGridLen δ) Cu) := by
  classical
  have hle : ∀ (k : ℕ) (i : ι) (x : E3),
      ((ShadedTube.shadeClass s T (𝒰.cover.assign k) (𝒰.cover.assign k i) x).card : NNReal)
        ≤ 1 := by
    intro k i x
    have hcard : (ShadedTube.shadeClass s T (𝒰.cover.assign k) (𝒰.cover.assign k i) x).card
        ≤ 1 := by
      refine Finset.card_le_one.mpr ?_
      intro a ha b hb
      have ha' := Finset.mem_filter.mp ha
      have hb' := Finset.mem_filter.mp hb
      have has : a ∈ s := (Finset.mem_filter.mp ha'.1).1
      have hbs : b ∈ s := (Finset.mem_filter.mp hb'.1).1
      by_contra hne
      exact Set.disjoint_left.mp (hdisj has hbs hne) ha'.2 hb'.2
    exact_mod_cast hcard
  have hge : ∀ (k : ℕ) (i : ι), i ∈ s → ∀ x : E3, x ∈ (T i).shade →
      (1 : NNReal) ≤
        ((ShadedTube.shadeClass s T (𝒰.cover.assign k)
          (𝒰.cover.assign k i) x).card : NNReal) := by
    intro k i hi x hx
    have hmem : i ∈ ShadedTube.shadeClass s T (𝒰.cover.assign k) (𝒰.cover.assign k i) x := by
      refine Finset.mem_filter.mpr ⟨?_, hx⟩
      exact Finset.mem_filter.mpr ⟨hi, rfl⟩
    have : 1 ≤ (ShadedTube.shadeClass s T (𝒰.cover.assign k) (𝒰.cover.assign k i) x).card :=
      Finset.card_pos.mpr ⟨i, hmem⟩
    exact_mod_cast this
  exact ⟨{ tubeUniform := 𝒰
           branchingN := fun _ => 1
           localN := fun _ _ => 1
           card_shadeClass_le := by
             intro x _ k _ i _ _
             exact le_trans (hle k i x) (by simpa using hCu)
           le_card_shadeClass := by
             intro x _ k _ i hi hxi
             exact le_trans (by simpa using hge k i hi x hxi)
               (le_mul_of_one_le_left (by positivity) hCu)
           branchingN_le := by
             intro x _ k _
             simpa using hCu
           le_branchingN := by
             intro x _ k _
             simpa using hCu }⟩

/-- The five binders of GWZ Lemma 9.1 that do not mention the `ρ`-count: ball, **centredness**,
bounded uniformity, `Δ_max ≤ δ^{-η}`, `λ ≥ δ^{η}`. -/
def Lemma91BindersNoCount (η : ℝ) {δ : NNReal} {ι : Type v} (s : Finset ι)
    (T : ι → ShadedTube δ E3) : Prop :=
  (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) ∧
  (∀ i ∈ s, (T i).toTube.IsCentred) ∧
  (∃ C : NNReal, 1 ≤ C ∧ (C : ENNReal) ≤ (δ : ENNReal) ^ (-η) ∧
    Nonempty (ShadedTube.ShadedUniformTubeSet s T (Tube.ssfGridLen δ) C)) ∧
  Kakeya.maxDensity s (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η) ∧
  ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η

/-- The sixth binder of GWZ Lemma 9.1: an essentially distinct, all-used `ρ`-family of at least
`ρ^{-2-ζ}` members at every scale of the window. -/
def Lemma91CountBinder (ϖ ζ : ℝ) {δ : NNReal} {ι : Type v} (s : Finset ι)
    (T : ι → ShadedTube δ E3) : Prop :=
  ∀ ρ : NNReal, ρ ∈ Set.Icc (δ ^ (1 - ϖ)) (δ ^ ϖ) →
    ∃ (κ : Type v) (tρ : Finset κ) (Tρ : κ → Tube ρ E3),
      (tρ : Set κ).Pairwise (fun j k ↦ IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) ∧
      (∀ j ∈ tρ, ∃ i ∈ s, (T i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) ∧
      (ρ : ℝ) ^ (-2 - ζ) ≤ (tρ.card : ℝ)

/-- **compatibility.**  The two `def`s above are the existing binder list of
`Kakeya.multiplicity_le_of_card_isEssDistinct_ge`: this is that theorem, restated through them.
It does not elaborate if either transcription is weaker than the tree's. -/
theorem lemma91_of_binders {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) :
    ∃ ϖ > (0:ℝ), ∀ ζ > (0:ℝ), ∃ ν > (0:ℝ), ∃ η > (0:ℝ),
      KatzTaoEstimate.{v} (EuclideanSpace ℝ (Fin 3)) β →
      FrostmanEstimate.{v} (EuclideanSpace ℝ (Fin 3)) β →
      ∀ᶠ (δ : NNReal) in nhdsWithin 0 (Set.Ioi 0),
      ∀ {ι : Type v} (s : Finset ι) (T : ι → ShadedTube δ E3),
        Lemma91BindersNoCount.{v} η s T → Lemma91CountBinder.{v} ϖ ζ s T →
        ShadedBody.multiplicity s (fun i ↦ (T i).toShadedBody)
          ≤ (δ : ENNReal) ^ ν * (s.card : ENNReal) ^ β := by
  obtain ⟨ϖ, hϖ, h⟩ := Kakeya.multiplicity_le_of_card_isEssDistinct_ge.{v} hβ hβ1
  refine ⟨ϖ, hϖ, fun ζ hζ => ?_⟩
  obtain ⟨ν, hν, η, hη, hmain⟩ := h ζ hζ
  refine ⟨ν, hν, η, hη, fun hKT hF => ?_⟩
  filter_upwards [hmain hKT hF] with δ hδ
  intro ι s T hb hc
  exact hδ s T hb.1 hb.2.1 hb.2.2.1 hb.2.2.2.1 hb.2.2.2.2 hc

/-- **W2.**  At arbitrarily small `δ` there is a family meeting every binder of GWZ Lemma 9.1
except the `ρ`-count: it is centred, uniform at an absolute constant (hence at `δ^{-η}`), of
density `≤ 1`, fully shaded, and has more than `δ^{-1}` members whose carriers are **pairwise
disjoint** — the property the axial refutation family maximally fails. -/
theorem exists_lemma91BindersNoCount_nonvacuity (η : ℝ) (hη : 0 < η) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : NNReal, 0 < δ ∧ (δ : ℝ) < ε ∧
      ∃ (ι : Type v) (s : Finset ι) (T : ι → ShadedTube δ E3),
        Lemma91BindersNoCount.{v} η s T ∧
        (δ : ℝ)⁻¹ ≤ (s.card : ℝ) ∧
        (s : Set ι).Pairwise (fun i j => Disjoint (T i).carrier (T j).carrier) := by
  classical
  set Cu₀ : NNReal := ShadedTube.ssfUniformConst (Module.finrank ℝ E3) with hCu₀def
  obtain ⟨M, s', V', hM1, hMA, hV'tube, hs'sub, hs'ne, hcards', ⟨𝒮⟩⟩ :=
    exists_gridWitness_half.{v} (max (ε⁻¹) (((Cu₀ : NNReal) : ℝ) ^ (1/η)))
  have hMε : ε⁻¹ < (M:ℝ) := lt_of_le_of_lt (le_max_left _ _) hMA
  have hMcu : ((Cu₀ : NNReal) : ℝ) ^ (1/η) < (M:ℝ) := lt_of_le_of_lt (le_max_right _ _) hMA
  have hMr : (1:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM1
  have hMpos : (0:ℝ) < (M:ℝ) := by linarith
  have hδpos : 0 < wδ M := wδ_pos hM1
  have hδlt1 : wδ M < 1 := wδ_lt_one hM1
  have hδle1 : wδ M ≤ 1 := le_of_lt hδlt1
  have hδr : (0:ℝ) < ((wδ M : NNReal):ℝ) := by rw [wδ_coe]; positivity
  refine ⟨wδ M, hδpos, wδ_lt_of_inv_lt hM1 hε hMε, ?_⟩
  have hFcar : ∀ i, (fullShade (V' i)).carrier = (wfam M i).carrier := fun i =>
    congrArg (fun t : Tube (wδ M) E3 => t.carrier) (hV'tube i)
  have hFtube : ∀ i, (fullShade (V' i)).toTube = (wcore M i.down) := fun i => hV'tube i
  have hFshade : ∀ i, (fullShade (V' i)).shade = (fullShade (V' i)).carrier := fun _ => rfl
  have hFdisj : ((s' : Finset (ULift.{v} (Fin M × Fin M))) :
      Set (ULift.{v} (Fin M × Fin M))).Pairwise
      fun i j => Disjoint (fullShade (V' i)).carrier (fullShade (V' j)).carrier := by
    intro i _ j _ hij
    rw [hFcar i, hFcar j]
    exact wfam_disjoint hM1 hij
  have hFmax : Kakeya.maxDensity s' (fun i => (fullShade (V' i)).toConvexSpaceBody) ≤ 1 :=
    maxDensity_le_one_of_disjoint (fun i => (fullShade (V' i)).toConvexSpaceBody) hFdisj
  have hFfull : ShadedBody.fullness s' (fun i => (fullShade (V' i)).toShadedBody) = 1 :=
    fullness_eq_one_of_fullShade hδpos hδle1 (fun i => fullShade (V' i))
      (fun i _ => hFshade i) hs'ne
  -- the absolute uniformity constant sits below `δ^{-η}`
  have hCuR : ((Cu₀ : NNReal) : ℝ) ≤ (24*(M:ℝ))^η := by
    have hA : ((((Cu₀ : NNReal) : ℝ)) ^ (1/η)) ^ η = ((Cu₀ : NNReal) : ℝ) := by
      rw [← Real.rpow_mul (by positivity), one_div, inv_mul_cancel₀ (ne_of_gt hη),
        Real.rpow_one]
    nth_rewrite 1 [← hA]
    refine Real.rpow_le_rpow (by positivity) ?_ hη.le
    linarith
  have hCuE : ((Cu₀ : NNReal) : ENNReal) ≤ ((wδ M : NNReal) : ENNReal) ^ (-η) := by
    have hne : (wδ M : NNReal) ≠ 0 := hδpos.ne'
    rw [← ENNReal.coe_rpow_of_ne_zero hne, ENNReal.coe_le_coe, ← NNReal.coe_le_coe,
      NNReal.coe_rpow, wδ_rpow_neg hM1]
    exact hCuR
  refine ⟨ULift.{v} (Fin M × Fin M), s', fun i => fullShade (V' i),
    ⟨?_, ?_, ⟨Cu₀, ShadedTube.one_le_ssfUniformConst _, hCuE, ?_⟩, ?_, ?_⟩, ?_, hFdisj⟩
  · intro i _
    rw [hFcar i]
    exact wfam_ball hM1 i
  · intro i _
    rw [hFtube i]
    exact wcore_isCentred M i.down
  · refine nonempty_shadedUniformTubeSet_of_disjoint (T := fun i => fullShade (V' i))
      𝒮.tubeUniform (ShadedTube.one_le_ssfUniformConst _) ?_
    intro i hi j hj hij
    rw [hFshade i, hFshade j]
    exact hFdisj hi hj hij
  · exact le_trans hFmax (one_le_rpow_neg_of_le_one hδle1 hη.le)
  · rw [hFfull]
    exact NNReal.rpow_le_one hδle1 hη.le
  · rw [wδ_inv hM1]
    exact hcards'


/-! ## The `ρ`-count binder is the one that is *not* jointly satisfiable

The five binders above are met by the grid family, and so is the trial.  The **count** binder is
different, and this section prices it exactly.  Two bounds meet:

* a `ρ`-tube of an all-used, essentially distinct family contains a member of `s`, and only
  `2 · 385^6` pairwise essentially distinct `ρ`-tubes can contain one and the same `δ`-tube
  (`Kakeya.VeryNotSticky.dist_endpoints_le_of_carrier_subset` pins their endpoints to `3ρ`-balls
  and `Kakeya.VeryNotSticky.card_le_of_ed_of_endpoints_confined` counts them), so
  `#𝕋_ρ ≤ 2 · 385^6 · #𝕋`;
* `Δ_max(𝕋) ≤ δ^{-η}` for a family in the unit ball forces `#𝕋 ≤ C₃ · δ^{-2-η}`
  (`Kakeya.Tube.card_le_of_densityIn_le`).

At the fine end `ρ = δ^{1-ϖ}` of the window the count binder asks for `δ^{-(1-ϖ)(2+ζ)}` of them.
So the binder list is **empty at every small `δ`** whenever `(1-ϖ)(2+ζ) > 2 + η`, i.e. whenever
`ζ > (η + 2ϖ)/(1-ϖ)`: for those exponents GWZ Lemma 9.1 is vacuously true. -/

open Kakeya.VeryNotSticky in
/-- Pairwise essentially distinct `ρ`-tubes that all contain one and the same `δ`-tube number at
most `2 · 385^6`. -/
theorem card_le_of_common_subtube {δ ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    {κ : Type*} (t : Finset κ) (Tρ : κ → Tube ρ E3) (W : Tube δ E3)
    (hsub : ∀ j ∈ t, W.carrier ⊆ (Tρ j).carrier)
    (hED : (t : Set κ).Pairwise fun j k => IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) :
    t.card ≤ 2 * 385 ^ 6 := by
  classical
  set P : κ → Prop := fun j => dist W.x (Tρ j).x ≤ 3 * (ρ:ℝ) ∧ dist W.y (Tρ j).y ≤ 3 * (ρ:ℝ)
    with hPdef
  have hEDmono : ∀ u : Finset κ, u ⊆ t →
      (u : Set κ).Pairwise fun j k => IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier := by
    intro u hu
    exact hED.mono (by exact_mod_cast hu)
  have hθ : ∀ j ∈ t.filter P, |(0:ℝ)| ≤ 1 / 288 := by
    intro j _
    norm_num
  have h1 : (t.filter P).card ≤ 385 ^ 6 := by
    refine card_le_of_ed_of_endpoints_confined hρ0 hρ1 (t.filter P) Tρ W.x W.y (fun _ => 0)
      hθ ?_ ?_ (hEDmono _ (Finset.filter_subset _ _))
    · intro j hj
      have hP := (Finset.mem_filter.mp hj).2
      simpa [dist_comm] using hP.1
    · intro j hj
      have hP := (Finset.mem_filter.mp hj).2
      simpa [dist_comm] using hP.2
  have h2 : (t.filter (fun j => ¬ P j)).card ≤ 385 ^ 6 := by
    have hθ' : ∀ j ∈ t.filter (fun j => ¬ P j), |(0:ℝ)| ≤ 1 / 288 := by
      intro j _
      norm_num
    have hQ : ∀ j ∈ t.filter (fun j => ¬ P j),
        dist W.x (Tρ j).y ≤ 3 * (ρ:ℝ) ∧ dist W.y (Tρ j).x ≤ 3 * (ρ:ℝ) := by
      intro j hj
      have hjt := (Finset.mem_filter.mp hj).1
      have hnP := (Finset.mem_filter.mp hj).2
      rcases dist_endpoints_le_of_carrier_subset W (Tρ j) (hsub j hjt) with h | h
      · exact absurd h hnP
      · exact h
    refine card_le_of_ed_of_endpoints_confined hρ0 hρ1 (t.filter (fun j => ¬ P j)) Tρ W.y W.x
      (fun _ => 0) hθ' ?_ ?_ (hEDmono _ (Finset.filter_subset _ _))
    · intro j hj
      simpa [dist_comm] using (hQ j hj).2
    · intro j hj
      simpa [dist_comm] using (hQ j hj).1
  have hsplit : (t.filter P).card + (t.filter (fun j => ¬ P j)).card = t.card :=
    Finset.filter_card_add_filter_neg_card_eq_card _
  omega

/-- **The all-used bound.**  A pairwise essentially distinct family of `ρ`-tubes each of which
contains a member of `s` has at most `2 · 385^6 · #s` members. -/
theorem card_used_le {δ ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    {ι : Type*} {κ : Type*} (s : Finset ι) (T : ι → ShadedTube δ E3)
    (tρ : Finset κ) (Tρ : κ → Tube ρ E3)
    (hED : (tρ : Set κ).Pairwise fun j k => IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier)
    (hused : ∀ j ∈ tρ, ∃ i ∈ s, (T i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) :
    tρ.card ≤ 2 * 385 ^ 6 * s.card := by
  classical
  rcases tρ.eq_empty_or_nonempty with rfl | ⟨j₀, hj₀⟩
  · simp
  obtain ⟨i₀, hi₀, -⟩ := hused j₀ hj₀
  haveI : Nonempty ι := ⟨i₀⟩
  choose! f hf1 hf2 using hused
  rw [Finset.card_eq_sum_card_fiberwise hf1]
  have hfib : ∀ i ∈ s, (tρ.filter (fun j => f j = i)).card ≤ 2 * 385 ^ 6 := by
    intro i _
    refine card_le_of_common_subtube hρ0 hρ1 _ Tρ (T i).toTube ?_ ?_
    · intro j hj
      have hjt := (Finset.mem_filter.mp hj).1
      have hfi := (Finset.mem_filter.mp hj).2
      have := hf2 j hjt
      rw [hfi] at this
      exact SetLike.coe_subset_coe.mpr this
    · exact hED.mono (by exact_mod_cast Finset.filter_subset _ _)
  calc ∑ i ∈ s, (tρ.filter (fun j => f j = i)).card
      ≤ ∑ _i ∈ s, 2 * 385 ^ 6 := Finset.sum_le_sum hfib
    _ = 2 * 385 ^ 6 * s.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- **The density bound.**  A family of `δ`-tubes in the unit ball with `Δ_max ≤ δ^{-η}` has at
most `C₃ · δ^{-η} · δ^{-2}` members. -/
theorem card_le_of_maxDensity {δ : NNReal} (hδ0 : 0 < δ) {η : ℝ}
    {ι : Type*} (s : Finset ι) (T : ι → ShadedTube δ E3)
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1)
    (hmax : Kakeya.maxDensity s (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η)) :
    (s.card : ℝ)
      ≤ ((Tube.card_le_of_densityIn_le.C 3 : NNReal) : ℝ) * (δ:ℝ) ^ (-η) * (δ:ℝ) ^ (-(2:ℝ)) := by
  have hE : Module.finrank ℝ E3 = 3 := by simp
  have hden : densityIn s (fun i ↦ (T i).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall
      ≤ (δ : ENNReal) ^ (-η) := (le_maxDensity s _ _).trans hmax
  have hraw := Tube.card_le_of_densityIn_le (E := E3) (δ := δ) (s := s)
    (T := fun i ↦ (T i).toTube) hδ0.ne' hball hden
  rw [hE] at hraw
  norm_num at hraw
  have hzpow : (δ : ENNReal) ^ (-2 : ℤ) = (δ : ENNReal) ^ (-2 : ℝ) := by
    rw [← ENNReal.rpow_intCast]
    norm_num
  rw [hzpow] at hraw
  rw [← ENNReal.coe_rpow_of_ne_zero hδ0.ne' (-η), ← ENNReal.coe_rpow_of_ne_zero hδ0.ne' (-2:ℝ),
    ← ENNReal.coe_mul, ← ENNReal.coe_mul,
    show ((s.card : ENNReal)) = ((s.card : NNReal) : ENNReal) by simp,
    ENNReal.coe_le_coe, ← NNReal.coe_le_coe] at hraw
  simpa [NNReal.coe_rpow] using hraw


open Filter Topology in
/-- **The count binder is empty for large `ζ`.**  If `(1-ϖ)(2+ζ) > 2 + η` then, at every
sufficiently small `δ`, *no* family at all meets both `Kakeya.ML2Wit.Lemma91BindersNoCount` and
`Kakeya.ML2Wit.Lemma91CountBinder`: the count asked for at the fine end `ρ = δ^{1-ϖ}` of the
window exceeds what `2 · 385^6 · #𝕋` can supply once `Δ_max ≤ δ^{-η}` caps `#𝕋` at
`C₃ δ^{-2-η}`.  For those exponents GWZ Lemma 9.1 is **vacuously** true, and the run's usable
tolerance range is `ζ ≤ (η + 2ϖ)/(1-ϖ)`. -/
theorem lemma91Binders_vacuous_of_exponents {ϖ ζ η : ℝ} (hϖ0 : 0 < ϖ)
    (hϖ : ϖ ≤ 1 / 2) (hgap : 2 + η < (1 - ϖ) * (2 + ζ)) :
    ∀ᶠ (δ : NNReal) in nhdsWithin 0 (Set.Ioi 0),
      ∀ {ι : Type v} (s : Finset ι) (T : ι → ShadedTube δ E3),
        Lemma91BindersNoCount.{v} η s T → ¬ Lemma91CountBinder.{v} ϖ ζ s T := by
  classical
  set Cd : ℝ := ((Tube.card_le_of_densityIn_le.C 3 : NNReal) : ℝ) with hCddef
  have hCd0 : (0:ℝ) ≤ Cd := (Tube.card_le_of_densityIn_le.C 3).coe_nonneg
  set Kc : ℝ := 2 * 385 ^ 6 * Cd with hKcdef
  have hKc0 : (0:ℝ) ≤ Kc := by rw [hKcdef]; positivity
  set γ : ℝ := (1 - ϖ) * (2 + ζ) - (2 + η) with hγdef
  have hγ : 0 < γ := by rw [hγdef]; linarith
  have hK1 : (0:ℝ) < Kc + 1 := by linarith
  set c : NNReal := (Real.toNNReal (Kc + 1))⁻¹ with hcdef
  have hKnn : (0:NNReal) < Real.toNNReal (Kc + 1) := Real.toNNReal_pos.mpr hK1
  have hc0 : (0:NNReal) < c := by rw [hcdef]; positivity
  have hd : (0:NNReal) < c ^ (1/γ) := NNReal.rpow_pos hc0
  filter_upwards [Ioo_mem_nhdsGT (lt_min hd (show (0:NNReal) < 1/2 by norm_num))] with δ hδ
  intro ι s T hb hc'
  obtain ⟨hball, hcen, huni, hmax, hfull⟩ := hb
  have hδ0 : 0 < δ := hδ.1
  have hδhalf : δ < 1/2 := lt_of_lt_of_le hδ.2 (min_le_right _ _)
  have hδ1 : δ ≤ 1 := le_of_lt (lt_of_lt_of_le hδhalf (by norm_num))
  have hδ0r : (0:ℝ) < (δ:ℝ) := by exact_mod_cast hδ0
  -- the threshold `Kc < δ^{-γ}`
  have hcpow : δ ^ γ ≤ c := by
    have h1 : δ ≤ c ^ (1/γ) := le_of_lt (lt_of_lt_of_le hδ.2 (min_le_left _ _))
    calc δ ^ γ ≤ (c ^ (1/γ)) ^ γ := NNReal.rpow_le_rpow h1 hγ.le
      _ = c := by rw [← NNReal.rpow_mul, one_div, inv_mul_cancel₀ hγ.ne', NNReal.rpow_one]
  have hcpowR : (δ:ℝ) ^ γ ≤ (Kc + 1)⁻¹ := by
    have h := NNReal.coe_le_coe.mpr hcpow
    rw [NNReal.coe_rpow, hcdef, NNReal.coe_inv, Real.coe_toNNReal _ (le_of_lt hK1)] at h
    exact h
  have hpowpos : (0:ℝ) < (δ:ℝ) ^ γ := Real.rpow_pos_of_pos hδ0r _
  have hid : (δ:ℝ) ^ γ * ((δ:ℝ) ^ γ)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hpowpos)
  have h3 : (δ:ℝ) ^ γ * (Kc + 1) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hcpowR (le_of_lt hK1)
    rwa [inv_mul_cancel₀ (ne_of_gt hK1)] at h
  have h4 : Kc + 1 ≤ ((δ:ℝ) ^ γ)⁻¹ := by
    by_contra hcon
    push_neg at hcon
    have hlt : (δ:ℝ) ^ γ * ((δ:ℝ) ^ γ)⁻¹ < (δ:ℝ) ^ γ * (Kc + 1) :=
      mul_lt_mul_of_pos_left hcon hpowpos
    rw [hid] at hlt
    linarith
  have hKlt : Kc < (δ:ℝ) ^ (-γ) := by
    rw [Real.rpow_neg (le_of_lt hδ0r)]
    linarith
  -- the count at the fine end of the window
  set ρ : NNReal := δ ^ (1 - ϖ) with hρdef
  have hρ0 : 0 < ρ := by rw [hρdef]; exact NNReal.rpow_pos hδ0
  have hρ1 : ρ ≤ 1 := by rw [hρdef]; exact NNReal.rpow_le_one hδ1 (by linarith)
  have hρmem : ρ ∈ Set.Icc (δ ^ (1 - ϖ)) (δ ^ ϖ) := by
    refine ⟨by rw [hρdef], ?_⟩
    rw [hρdef]
    exact NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (by linarith)
  obtain ⟨κ, tρ, Tρ, hED, hused, hcount⟩ := hc' ρ hρmem
  have hcard1 : tρ.card ≤ 2 * 385 ^ 6 * s.card := card_used_le hρ0 hρ1 s T tρ Tρ hED hused
  have hcard1R : (tρ.card : ℝ) ≤ 2 * 385 ^ 6 * (s.card : ℝ) := by exact_mod_cast hcard1
  have hcard2 : (s.card : ℝ) ≤ Cd * (δ:ℝ) ^ (-η) * (δ:ℝ) ^ (-(2:ℝ)) :=
    card_le_of_maxDensity hδ0 s T hball hmax
  have hexp : (1 - ϖ) * (-2 - ζ) = -γ + -(2 + η) := by rw [hγdef]; ring
  have hρpow : (ρ:ℝ) ^ (-2 - ζ) = (δ:ℝ) ^ (-γ) * (δ:ℝ) ^ (-(2 + η)) := by
    rw [hρdef, NNReal.coe_rpow, ← Real.rpow_mul (le_of_lt hδ0r), hexp,
      Real.rpow_add hδ0r]
  have hd2 : (δ:ℝ) ^ (-η) * (δ:ℝ) ^ (-(2:ℝ)) = (δ:ℝ) ^ (-(2 + η)) := by
    rw [← Real.rpow_add hδ0r]
    ring_nf
  have hpos2 : (0:ℝ) < (δ:ℝ) ^ (-(2 + η)) := Real.rpow_pos_of_pos hδ0r _
  have hfinal : (δ:ℝ) ^ (-γ) * (δ:ℝ) ^ (-(2 + η)) ≤ Kc * (δ:ℝ) ^ (-(2 + η)) := by
    rw [← hρpow]
    calc (ρ:ℝ) ^ (-2 - ζ) ≤ (tρ.card : ℝ) := hcount
      _ ≤ 2 * 385 ^ 6 * (s.card : ℝ) := hcard1R
      _ ≤ 2 * 385 ^ 6 * (Cd * (δ:ℝ) ^ (-η) * (δ:ℝ) ^ (-(2:ℝ))) := by
          have h0 : (0:ℝ) ≤ 2 * 385 ^ 6 := by norm_num
          exact mul_le_mul_of_nonneg_left hcard2 h0
      _ = Kc * (δ:ℝ) ^ (-(2 + η)) := by rw [hKcdef, ← hd2]; ring
  have hle : (δ:ℝ) ^ (-γ) ≤ Kc := le_of_mul_le_mul_right hfinal hpos2
  linarith


/-- The obstruction is itself not vacuous: at `ϖ = 1/10`, `η = 1/100` it already bites at
`ζ = 1`. -/
theorem vacuity_range_nonempty :
    (0:ℝ) < 1/10 ∧ (1/10:ℝ) ≤ 1/2 ∧ (0:ℝ) ≤ 1/100 ∧
      (2:ℝ) + 1/100 < (1 - 1/10) * (2 + 1) := by
  norm_num


/-! ## W1′ — the closing skeleton's `SiteWitness`, and the `K` this family admits

`Kakeya.ML2Core.SiteWitness` (`Reduction/SpineSiteClosure.lean:87–106`, `md5sum` of those lines
`19559d0d5eb7ebd9d9db4b35d9050900`) is the *downward* re-cut of the row list: four data
existentials (`u'`, `Cu`/`𝒰`, `lam`, `K`), ten rows, and **no `ε₀'`/`g'`** — the skeleton picks the
exit exponents itself and discharges all four absorption rows internally.  The one non-trivial row
is the outer margin budget `K · δ^(dm − aL) ≤ 1`, where `α ≤ dm − aL ≤ β/48000` bites.

**Measured: this family admits `K = 1`.**  Take `u' := s` — the *ambient* family of the witness is
already the uniformisation's retained subfamily, so nothing has to be retained a second time — and
`lam := 1`.  `Kakeya.ML2Core.stateMass` ignores the shading level
(`Kakeya.ML2Core.stateMass_level`), so `stateMass (s,T,1) = stateMass (u',T,lam)` **on the nose**
and the ledger holds at `K = 1` with no `δ`-power at all.  Row 10 is then
`δ^(dm − aL) ≤ 1`, i.e. exactly `aL ≤ dm`.  So the `α = β/4` failure of the earlier reading is not
a property of the family: it was an artefact of putting the *full grid* in the ambient slot and
paying `δ^{-β/4}` to retain a uniform subfamily.

**Caveat — this says nothing about the site's producer.**  `u' = s`, `lam = 1`, `K = 1` puts the
retention exponent at `α = 0`, trivially inside the budget `α ≤ dm − aL ≤ β/48000`.  That is exactly
right for *non-vacuity*, and exactly wrong as evidence about the real site, which has `u' ⊊ s` and
`K > 1` — there the budget row **binds**, and it is the row a producer has to be designed against
(`Kakeya.ML2Core.absorbK_of_budget` is where everything reduces to `K · δ^(dm − aL) ≤ 1`).  A
witness shows the row list is inhabited; it does not show the site can inhabit it *while retaining a
proper subfamily*, which is the site's actual difficulty.

The side conditions `aL ≤ ηin` and `aL ≤ dm` are universally quantified here, not chosen, so the
witness covers the skeleton's whole admissible window `aL ∈ (0, min ηin dm]`; the hypothesis is
stated at `0 ≤ aL`, which is *weaker* than the skeleton's strict `0 < aL`
(`Kakeya.ML2Core.geometricCoreAt_of_witness_and_trial` instantiates `T-D5` at `aL`), so no
instantiation is lost. -/

open Kakeya.ML2Core in
/-- The `∃`-block of `Kakeya.ML2Core.SiteWitness`, transcribed from
`SpineSiteClosure.lean:94–106` (source pin `19559d0d5eb7ebd9d9db4b35d9050900` over `:87–106`). -/
def SiteWitnessRows (ηin dm aL : ℝ) (Cu₀ : NNReal) {δ : NNReal} {ι : Type v}
    (s : Finset ι) (T : ι → ShadedTube δ E3) : Prop :=
      ∃ u' : Finset ι, u' ⊆ s ∧
      ∃ (Cu : NNReal) (_ : Tube.UniformTubeSet u' (fun i => (T i).toTube)
          (Tube.ssfGridLen δ) Cu) (lam : NNReal) (K : ℝ≥0∞),
        Cu ≤ Cu₀ ∧
        (s.card : ℝ) ≤ (δ : ℝ) ^ (-(4 : ℝ)) ∧
        u'.Nonempty ∧
        Kakeya.maxDensity u' (fun i => (T i).toConvexSpaceBody) ≤ (δ : ℝ≥0∞) ^ (-ηin) ∧
        0 < lam ∧
        ML2Shaded.HasDenseShading lam u' (fun i => (T i).toShadedBody) ∧
        (((δ : NNReal) ^ (ηin - aL) / 2 : NNReal) : ℝ≥0∞) ≤ (lam : ℝ≥0∞) ∧
        stateMass ((s, T, (1 : NNReal)) : DescentState ι δ)
          ≤ K * stateMass ((u', T, lam) : DescentState ι δ) ∧
        K * (δ : ℝ≥0∞) ^ (dm - aL) ≤ 1

/-- `Kakeya.ML2Core.SiteWitness` itself, transcribed.  Once `SpineSiteClosure.lean` is in the tree
the compatibility is
`example : SiteWitnessPred.{v} η ηin dm aL Cu₀ → ML2Core.SiteWitness.{v} η ηin dm aL Cu₀ := id`;
until then the tie is the source pin on the row block. -/
def SiteWitnessPred (η ηin dm aL : ℝ) (Cu₀ : NNReal) : Prop :=
  ∀ᶠ (δ : NNReal) in nhdsWithin 0 (Set.Ioi 0),
    ∀ {ι : Type v} (s : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) →
      IsKatzTao s (fun i => (T i).toConvexSpaceBody) ((δ : ℝ≥0∞) ^ (-η)) →
      ShadedBody.fullness s (fun i => (T i).toShadedBody) ≥ δ ^ η →
      (δ : ℝ)⁻¹ ≤ (s.card : ℝ) →
      SiteWitnessRows.{v} ηin dm aL Cu₀ s T

/-- **compatibility.**  `Kakeya.ML2Wit.SiteWitnessPred` is `Kakeya.ML2Core.SiteWitness` on the nose —
`id`, no bridge.  If either transcription drifts, this `example` stops elaborating.  Measured
firing control: perturbing one row (`Cu ≤ Cu₀` to `Cu ≤ Cu₀ + 1`) makes it fail with a type
mismatch. -/
example (η ηin dm aL : ℝ) (Cu₀ : NNReal) :
    SiteWitnessPred.{v} η ηin dm aL Cu₀ → ML2Core.SiteWitness.{v} η ηin dm aL Cu₀ := id

/-- **W1′.**  The row block of `Kakeya.ML2Core.SiteWitness` is inhabited at arbitrarily small `δ`,
at the **absolute** `Cu₀ = ssfUniformConst 3` and with `K = 1`: the outer margin row costs nothing,
so the witness survives the `α ≤ dm − aL ≤ β/48000` cap with room to spare.  The two conditions are
the ones the supplier chooses anyway: `aL ≤ ηin` (row 7) and `aL ≤ dm` (row 10).

`SiteWitness` itself is a `∀`-statement over *every* admissible family — that is the site's
obligation, not a witness's.  What is certified here is its non-vacuity: the inner `∀ s T` is not
empty on any tail, so the skeleton cannot be fed a vacuously-true `SiteWitness`. -/
theorem exists_siteWitness_nonvacuity :
    ∃ Cu₀ : NNReal,
      ∀ (η ηin dm aL : ℝ), 0 ≤ η → 0 ≤ aL → aL ≤ ηin → aL ≤ dm → ∀ ε : ℝ, 0 < ε →
        ∃ δ : NNReal, 0 < δ ∧ (δ : ℝ) < ε ∧
          ∃ (ι : Type v) (s : Finset ι) (T : ι → ShadedTube δ E3),
            SiteInputs.{v} η s T ∧ SiteWitnessRows.{v} ηin dm aL Cu₀ s T := by
  classical
  refine ⟨ShadedTube.ssfUniformConst (Module.finrank ℝ E3), ?_⟩
  intro η ηin dm aL hη0 haL0 haLηin haLdm ε hε
  obtain ⟨M, s', V', hM1, hMA, hV'tube, hs'sub, hs'ne, hcards', ⟨𝒮⟩⟩ :=
    exists_gridWitness_half.{v} (ε⁻¹)
  have hMr : (1:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM1
  have hMpos : (0:ℝ) < (M:ℝ) := by linarith
  have hδpos : 0 < wδ M := wδ_pos hM1
  have hδlt1 : wδ M < 1 := wδ_lt_one hM1
  have hδle1 : wδ M ≤ 1 := le_of_lt hδlt1
  refine ⟨wδ M, hδpos, wδ_lt_of_inv_lt hM1 hε hMA, ?_⟩
  have hFcar : ∀ i, (fullShade (V' i)).carrier = (wfam M i).carrier := fun i =>
    congrArg (fun t : Tube (wδ M) E3 => t.carrier) (hV'tube i)
  have hFshade : ∀ i, (fullShade (V' i)).shade = (fullShade (V' i)).carrier := fun _ => rfl
  have hFdisj : ((s' : Finset (ULift.{v} (Fin M × Fin M))) :
      Set (ULift.{v} (Fin M × Fin M))).Pairwise
      fun i j => Disjoint (fullShade (V' i)).carrier (fullShade (V' j)).carrier := by
    intro i _ j _ hij
    rw [hFcar i, hFcar j]
    exact wfam_disjoint hM1 hij
  have hFmax : Kakeya.maxDensity s' (fun i => (fullShade (V' i)).toConvexSpaceBody) ≤ 1 :=
    maxDensity_le_one_of_disjoint (fun i => (fullShade (V' i)).toConvexSpaceBody) hFdisj
  have hFfull : ShadedBody.fullness s' (fun i => (fullShade (V' i)).toShadedBody) = 1 :=
    fullness_eq_one_of_fullShade hδpos hδle1 (fun i => fullShade (V' i))
      (fun i _ => hFshade i) hs'ne
  have hcarduniv : ((Finset.univ : Finset (ULift.{v} (Fin M × Fin M))).card : ℝ)
      = (M:ℝ) * (M:ℝ) := by simp [Finset.card_univ]
  have hcard4 : (s'.card : ℝ) ≤ ((wδ M : NNReal):ℝ) ^ (-(4:ℝ)) := by
    rw [wδ_rpow_neg hM1]
    have h4 : ((24:ℝ)*(M:ℝ))^(4:ℝ)
        = ((24*(M:ℝ))*(24*(M:ℝ)))*((24*(M:ℝ))*(24*(M:ℝ))) := by
      rw [show (4:ℝ) = ((4:ℕ):ℝ) by norm_num, Real.rpow_natCast]; ring
    have hsle : (s'.card : ℝ) ≤ (M:ℝ)*(M:ℝ) := by
      have h := Finset.card_le_card hs'sub
      have h' : ((s'.card : ℕ) : ℝ)
          ≤ ((Finset.univ : Finset (ULift.{v} (Fin M × Fin M))).card : ℝ) := by exact_mod_cast h
      rw [hcarduniv] at h'
      exact h'
    rw [h4]
    have hA : (1:ℝ) ≤ 24*(M:ℝ) := by linarith
    have h1 : (M:ℝ)*(M:ℝ) ≤ (24*(M:ℝ))*(24*(M:ℝ)) := by nlinarith
    have hX : (1:ℝ) ≤ (24*(M:ℝ))*(24*(M:ℝ)) := by nlinarith
    have h2 : (24*(M:ℝ))*(24*(M:ℝ))
        ≤ ((24*(M:ℝ))*(24*(M:ℝ)))*((24*(M:ℝ))*(24*(M:ℝ))) := by nlinarith
    linarith
  refine ⟨ULift.{v} (Fin M × Fin M), s', fun i => fullShade (V' i), ⟨?_, ?_, ?_, ?_⟩,
    s', Finset.Subset.refl s', ShadedTube.ssfUniformConst (Module.finrank ℝ E3),
    𝒮.tubeUniform, 1, 1, le_rfl, hcard4, hs'ne, ?_, one_pos, ?_, ?_, ?_, ?_⟩
  · intro i _
    rw [hFcar i]
    exact wfam_ball hM1 i
  · exact le_trans hFmax (one_le_rpow_neg_of_le_one hδle1 hη0)
  · rw [hFfull]
    exact NNReal.rpow_le_one hδle1 hη0
  · rw [wδ_inv hM1]
    exact hcards'
  · exact le_trans hFmax (one_le_rpow_neg_of_le_one hδle1 (by linarith))
  · intro i _
    refine le_of_eq ?_
    rw [ENNReal.coe_one, one_mul]
    rfl
  · -- `δ^(ηin − aL)/2 ≤ 1`
    have h1 : (wδ M) ^ (ηin - aL) ≤ 1 := NNReal.rpow_le_one hδle1 (by linarith)
    have h2 : ((wδ M) ^ (ηin - aL) / 2 : NNReal) ≤ 1 := by
      exact le_trans (div_le_self (by positivity) (by norm_num)) h1
    exact_mod_cast h2
  · -- the ledger, at `K = 1`
    exact le_of_eq (one_mul _).symm
  · -- the outer margin budget, at `K = 1`
    rw [one_mul]
    exact ENNReal.rpow_le_one (by exact_mod_cast hδle1) (by linarith)

end Kakeya.ML2Wit

/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.SetupIslandRefute

/-!
# The flat-island refutation, reduced to a **carrier-level** witness

`Kakeya.VeryNotSticky.not_setupCaseSideDataStatement_of_flat_island` refutes
`Kakeya.VeryNotSticky.SetupCaseSideDataStatement` from a witness family that is *flat* and
*islanded*, but its hypothesis quantifies over **shaded** tubes: it demands a shading with an
exact per-tube mass, an isolated positive-measure island for every member, and — the expensive
clause — a `ShadedTube.ShadedUniformTubeSet` bundle.

This file removes all three demands.  The witness it needs is a family of **carriers** only,
plus a *hole system*: for each member a ball of radius `r₁ = δ^exscal` that the member meets,
such that no member loses more than a `1 - δ^η` fraction of its carrier to the union of the
`4 r₁`-holes.  The shading is then **constructed**, not assumed
(`Kakeya.VeryNotSticky.exists_flatIsland_shading`), and the refutation reduces to
`Kakeya.VeryNotSticky.not_setupCaseSideDataStatement_of_carrier_holes`.

Two facts make that possible, and the first is a fidelity finding in its own right.

**(1) The uniformity binder of the pre-F12a target was free.**
`Kakeya.VeryNotSticky.exists_shadedUniformTubeSet_of_axes_injOn`: for *any* finite family of
shaded `δ`-tubes with pairwise distinct axes and *any* shading whatsoever, the old binder
`∃ C : NNReal, Nonempty (ShadedTube.ShadedUniformTubeSet s T (Tube.ssfGridLen δ) C)` holds —
take the hierarchy in which every member is its own node at every grid scale, `branchingN ≡ 1`,
`localN ≡ 1`, and `C = |s| + 1`.  The constant `C` was existentially quantified with **no upper
bound**, whereas GWZ Definition 2.2 is used with `C ⪆ 1`, subpolynomial in `1/δ`.  So that
binder constrained the family not at all.  The target instead requires `∃ C, 1 ≤ C ∧ C ≤ δ^{-η} ∧ Nonempty …`, and on every Lemma 9.1 input
(`δ⁻¹ ≤ |s|`) the free witness `|s| + 1` exceeds `δ^{-η}`.  The two records of this file therefore
refute the frozen pre-F12a statement `Kakeya.VeryNotSticky.SetupCaseSideDataStatementOld`, whose
binder their witness still discharges; against the live statement the carrier-hole family would
additionally have to be uniform at a sub-polynomial constant, which is GWZ's own hypothesis.

**(2) Exact-measure subsets exist** (`Kakeya.VeryNotSticky.exists_subset_volume_eq`): a bounded
measurable subset of `ℝ³` has, for every `m` below its volume, a measurable subset of volume
exactly `m`.  Proved by the intermediate value theorem applied to
`r ↦ |A ∩ B̄(0,r)|`, which is Lipschitz on `[0,R]` because the volume of a ball is `c r³`.
Exactness is not a convenience: the aggregate binder `hfull` forces
`∑ |Y(T)| ≥ δ^η ∑ |T|` while flatness forces `|Y(T)| ≤ δ^η |T|` termwise, so every member is
`δ^η`-full *on the nose* — that rigidity is exactly what
`Kakeya.VeryNotSticky.volume_shade_eq_of_fullness_ge` runs on.

**What is left of the witness.**  After this file the obligation is: a family of `δ`-tubes in
`B_1`, with distinct axes, `Δ_max ≤ δ^{-η}` and the `ρ`-count `|𝕋_ρ| ≥ ρ^{-2-ζ}` over the
window, carrying a hole system.  The first three clauses are precisely the *carrier* hypotheses
of GWZ Lemma 9.1 itself — i.e. that lemma's own non-vacuity — and the hole system is a
placement statement about `r₁`-balls, not a statement about shadings.

**Retired clauses.**  Both refutations below are records, in the hoisted form of
`Kakeya.VeryNotSticky.RigidFullnessField`: they take the old `fullness_ge` and — because `Kakeya.VeryNotSticky.BallData.P_cover` to the working shading `Y_g` —
the old covering clause `Kakeya.VeryNotSticky.UniformShadingCoverField` as hypotheses.  Against
the live `BallData` an island of `Y(T) \ Y_g(T)` need not meet any piece, so the refutation does
not run; see the header of `Kakeya.DimensionThree.MainLemma2.SetupIslandRefute`.
-/

@[expose] public section

namespace Kakeya.VeryNotSticky

open MeasureTheory Metric Set Topology Filter ShadedBody

universe u

/-- The ambient space of Section 9. -/
local notation "E3" => EuclideanSpace ℝ (Fin 3)


private lemma finrank_euclidean3_s9 : Module.finrank ℝ E3 = 3 := by
  simp

/-- The volume of a closed ball in `E3`. -/
private lemma volume_closedBall_euclidean3_s9 (x : E3) {r : ℝ} (hr : 0 ≤ r) :
    volume (closedBall x r) = ENNReal.ofReal (r ^ 3) * volume (ball (0 : E3) 1) := by
  rw [MeasureTheory.Measure.addHaar_closedBall volume x hr, finrank_euclidean3_s9]

/-- **Exact-measure subsets exist.**  Any bounded measurable subset of `E3` has, for each
`m ≤ |A|`, a measurable subset of measure exactly `m`. -/
theorem exists_subset_volume_eq {A : Set E3} (hA : MeasurableSet A) {R : ℝ} (hR : 0 ≤ R)
    (hAR : A ⊆ closedBall 0 R) {m : ENNReal} (hm : m ≤ volume A) :
    ∃ S, MeasurableSet S ∧ S ⊆ A ∧ volume S = m := by
  classical
  set c : ℝ := (volume (ball (0 : E3) 1)).toReal with hc_def
  have hc0 : 0 ≤ c := ENNReal.toReal_nonneg
  have hball_top : volume (ball (0 : E3) 1) ≠ ⊤ := measure_ball_lt_top.ne
  have hfin : ∀ r : ℝ, volume (A ∩ closedBall (0 : E3) r) ≠ ⊤ := by
    intro r
    exact ne_top_of_le_ne_top measure_closedBall_lt_top.ne (measure_mono inter_subset_right)
  set g : ℝ → ℝ := fun r => (volume (A ∩ closedBall (0 : E3) r)).toReal with hg_def
  -- monotone
  have hgmono : Monotone g := by
    intro x y hxy
    exact ENNReal.toReal_mono (hfin y)
      (measure_mono (inter_subset_inter_right _ (closedBall_subset_closedBall hxy)))
  -- increment bound
  have hincr : ∀ x y : ℝ, 0 ≤ x → x ≤ y → g y - g x ≤ c * (y ^ 3 - x ^ 3) := by
    intro x y hx hxy
    have hy : 0 ≤ y := le_trans hx hxy
    have hsub : A ∩ closedBall (0 : E3) y ⊆
        (A ∩ closedBall (0 : E3) x) ∪ (closedBall (0 : E3) y \ closedBall (0 : E3) x) := by
      intro z hz
      by_cases hzx : z ∈ closedBall (0 : E3) x
      · exact Or.inl ⟨hz.1, hzx⟩
      · exact Or.inr ⟨hz.2, hzx⟩
    have hdiff : volume (closedBall (0 : E3) y \ closedBall (0 : E3) x)
        = volume (closedBall (0 : E3) y) - volume (closedBall (0 : E3) x) :=
      measure_sdiff (closedBall_subset_closedBall hxy)
        measurableSet_closedBall.nullMeasurableSet measure_closedBall_lt_top.ne
    have hle : volume (A ∩ closedBall (0 : E3) y)
        ≤ volume (A ∩ closedBall (0 : E3) x)
          + (volume (closedBall (0 : E3) y) - volume (closedBall (0 : E3) x)) := by
      calc volume (A ∩ closedBall (0 : E3) y)
          ≤ volume ((A ∩ closedBall (0 : E3) x) ∪
              (closedBall (0 : E3) y \ closedBall (0 : E3) x)) := measure_mono hsub
        _ ≤ volume (A ∩ closedBall (0 : E3) x)
              + volume (closedBall (0 : E3) y \ closedBall (0 : E3) x) := measure_union_le _ _
        _ = _ := by rw [hdiff]
    have hballfin : ∀ r : ℝ, volume (closedBall (0 : E3) r) ≠ ⊤ := fun r =>
      measure_closedBall_lt_top.ne
    have hcalc : (volume (closedBall (0 : E3) y) - volume (closedBall (0 : E3) x)).toReal
        = c * (y ^ 3 - x ^ 3) := by
      rw [ENNReal.toReal_sub_of_le
        (measure_mono (closedBall_subset_closedBall hxy)) (hballfin y),
        volume_closedBall_euclidean3_s9 (0 : E3) hy, volume_closedBall_euclidean3_s9 (0 : E3) hx]
      rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
        ENNReal.toReal_ofReal (by positivity)]
      ring
    have := ENNReal.toReal_mono
      (by
        exact ENNReal.add_ne_top.2 ⟨hfin x, ne_top_of_le_ne_top (hballfin y) tsub_le_self⟩) hle
    rw [ENNReal.toReal_add (hfin x) (ne_top_of_le_ne_top (hballfin y) tsub_le_self), hcalc] at this
    linarith
  -- Lipschitz on [0, R]
  have hlip : LipschitzOnWith (Real.toNNReal (3 * R ^ 2 * c)) g (Icc 0 R) := by
    refine LipschitzOnWith.of_dist_le_mul ?_
    intro x hx y hy
    have hK : ((Real.toNNReal (3 * R ^ 2 * c) : NNReal) : ℝ) = 3 * R ^ 2 * c := by
      rw [Real.coe_toNNReal]
      positivity
    rw [hK, Real.dist_eq, Real.dist_eq]
    rcases le_total x y with h | h
    · have h1 : g y - g x ≤ c * (y ^ 3 - x ^ 3) := hincr x y hx.1 h
      have h2 : y ^ 3 - x ^ 3 ≤ 3 * R ^ 2 * (y - x) := by
        have hfac : y ^ 3 - x ^ 3 = (y - x) * (y ^ 2 + x * y + x ^ 2) := by ring
        rw [hfac]
        have hxR : x ≤ R := hx.2
        have hyR : y ≤ R := hy.2
        have hx0 : 0 ≤ x := hx.1
        have hy0 : 0 ≤ y := hy.1
        have : y ^ 2 + x * y + x ^ 2 ≤ 3 * R ^ 2 := by nlinarith
        nlinarith [sub_nonneg.2 h]
      have h3 : 0 ≤ g y - g x := sub_nonneg.2 (hgmono h)
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
      nlinarith
    · have h1 : g x - g y ≤ c * (x ^ 3 - y ^ 3) := hincr y x hy.1 h
      have h2 : x ^ 3 - y ^ 3 ≤ 3 * R ^ 2 * (x - y) := by
        have hfac : x ^ 3 - y ^ 3 = (x - y) * (x ^ 2 + x * y + y ^ 2) := by ring
        rw [hfac]
        have : x ^ 2 + x * y + y ^ 2 ≤ 3 * R ^ 2 := by nlinarith [hx.1, hy.1, hx.2, hy.2]
        nlinarith [sub_nonneg.2 h]
      have h3 : 0 ≤ g x - g y := sub_nonneg.2 (hgmono h)
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      nlinarith
  -- endpoints
  have hg0 : g 0 = 0 := by
    have hz : volume (A ∩ ({0} : Set E3)) = 0 :=
      measure_mono_null inter_subset_right (measure_singleton _)
    simp [hg_def, hz]
  have hgR : g R = (volume A).toReal := by
    have : A ∩ closedBall (0 : E3) R = A := inter_eq_left.2 hAR
    rw [hg_def]
    simp [this]
  have hAfin : volume A ≠ ⊤ :=
    ne_top_of_le_ne_top measure_closedBall_lt_top.ne (measure_mono hAR)
  have hmfin : m ≠ ⊤ := ne_top_of_le_ne_top hAfin hm
  have hmem : m.toReal ∈ Icc (g 0) (g R) := by
    rw [hg0, hgR]
    exact ⟨ENNReal.toReal_nonneg, ENNReal.toReal_mono hAfin hm⟩
  obtain ⟨r, hrmem, hr⟩ := intermediate_value_Icc hR hlip.continuousOn hmem
  refine ⟨A ∩ closedBall (0 : E3) r, hA.inter measurableSet_closedBall, inter_subset_left, ?_⟩
  have := hr
  rw [hg_def] at this
  simp only at this
  exact (ENNReal.toReal_eq_toReal_iff' (hfin r) hmfin).1 this



/-- `δ ≤ δ^{k/N}` for `k ≤ N`. -/
private lemma delta_le_gridScale_s9 {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {N k : ℕ} (hk : k ≤ N) :
    δ ≤ Tube.gridScale δ N k := by
  have hratio : (k : ℝ) / (N : ℝ) ≤ 1 := by
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · interval_cases k
      · norm_num
    · rw [div_le_one (by exact_mod_cast hN)]
      exact_mod_cast hk
  have := NNReal.rpow_le_rpow_of_exponent_ge hδ hδ1 hratio
  simpa [Tube.gridScale] using this

/-- **The uniformity binder of `Kakeya.VeryNotSticky.exists_setup_caseSideData` is free.**

For *any* finite family of shaded `δ`-tubes with pairwise distinct axes there is a constant `C`
for which `ShadedTube.ShadedUniformTubeSet s V N C` is inhabited: take the hierarchy in which
every member is its own node at every grid scale (`assign k i = i`, node tube
`(V i).rescale (gridScale δ N k)`), `branchingN ≡ 1`, `localN ≡ 1`, and `C = |s| + 1`.

The binder `(∃ C : NNReal, Nonempty (ShadedTube.ShadedUniformTubeSet s T (Tube.ssfGridLen δ) C))`
of the pre-F12a target therefore carried **no information about the family**: `C` was
existentially quantified with no upper bound, whereas GWZ Definition 2.2 is used with `C ⪆ 1`
(subpolynomial in `1/δ`).  This is the same defect shape as a `⪆` rendered without its
constant, here on a *hypothesis*: it made the target harder to prove, and it made any
counterexample family cheaper to build.  The target bounds the constant by
`1 ≤ C ≤ δ^{-η}`, which this witness fails as soon as `δ⁻¹ ≤ |s|`; the old form is frozen as
`Kakeya.VeryNotSticky.SetupCaseSideDataStatementOld`. -/
theorem exists_shadedUniformTubeSet_of_axes_injOn {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {ι : Type*} (s : Finset ι) (V : ι → ShadedTube δ E3) (N : ℕ)
    (hinj : ∀ i ∈ s, ∀ j ∈ s, (V i).x = (V j).x → (V i).y = (V j).y → i = j) :
    ∃ C : NNReal, Nonempty (ShadedTube.ShadedUniformTubeSet s V N C) := by
  classical
  refine ⟨(s.card : NNReal) + 1, ⟨?_⟩⟩
  have hC1 : (1 : NNReal) ≤ (s.card : NNReal) + 1 := by simp
  have hcard_le : ∀ t : Finset ι, t ⊆ s → ((t.card : NNReal)) ≤ (s.card : NNReal) + 1 := by
    intro t ht
    have : t.card ≤ s.card := Finset.card_le_card ht
    calc ((t.card : NNReal)) ≤ (s.card : NNReal) := by exact_mod_cast this
      _ ≤ (s.card : NNReal) + 1 := le_self_add
  -- the trivial grid cover system: each member is its own node at every scale
  let cov : Tube.GridCoverSystem s (fun i => (V i).toTube) N :=
    { indexSet := fun _ => s
      assign := fun _ i => i
      tube := fun k i => (V i).toTube.rescale (Tube.gridScale δ N k)
      assign_mem := by intro k hk i hi; exact hi
      le_tube_assign := by
        intro k hk i hi
        exact Tube.le_rescale _ (delta_le_gridScale_s9 hδ hδ1 hk)
      nested := by intro k hk i hi j hj h; exact h
      tube_nested := by
        intro k hk i hi
        exact Tube.rescale_le_rescale_of_radius_le _
          (Tube.gridScale_antitone hδ hδ1 N (Nat.le_succ k)) }
  have hclass : ∀ (k : ℕ) (j : ι), j ∈ s →
      Tube.coverClass s (cov.assign k) j = {j} := by
    intro k j hj
    ext a
    simp only [Tube.coverClass, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨-, h⟩
      exact h
    · rintro rfl
      exact ⟨hj, rfl⟩
  have hclass_sub : ∀ (k : ℕ) (j : ι), Tube.coverClass s (cov.assign k) j ⊆ s := by
    intro k j
    simp only [Tube.coverClass]
    exact Finset.filter_subset _ _
  let unif : Tube.UniformTubeSet s (fun i => (V i).toTube) N ((s.card : NNReal) + 1) :=
    { cover := cov
      branchingN := fun _ => 1
      tube_injOn := by
        intro k hk i hi j hj hij
        have hij' : (V i).toTube.rescale (Tube.gridScale δ N k)
            = (V j).toTube.rescale (Tube.gridScale δ N k) := hij
        have hx : (V i).x = (V j).x := congrArg (fun T : Tube (Tube.gridScale δ N k) E3 => T.x) hij'
        have hy : (V i).y = (V j).y := congrArg (fun T : Tube (Tube.gridScale δ N k) E3 => T.y) hij'
        exact hinj i hi j hj hx hy
      boundedOverlap := by
        intro k hk W
        exact_mod_cast hcard_le _ (Finset.filter_subset _ _)
      card_class_le := by
        intro k hk j hj
        rw [mul_one]
        exact hcard_le _ (hclass_sub k j)
      le_card_class := by
        intro k hk j hj
        rw [hclass k j hj]
        simp }
  exact
    { tubeUniform := unif
      branchingN := fun _ => 1
      localN := fun _ _ => 1
      card_shadeClass_le := by
        intro x hx k hk i hi hxi
        rw [mul_one]
        refine hcard_le _ ?_
        exact (ShadedTube.shadeClass_subset s V (unif.cover.assign k) _ x).trans
          (hclass_sub k _)
      le_card_shadeClass := by
        intro x hx k hk i hi hxi
        have hmem : i ∈ ShadedTube.shadeClass s V (unif.cover.assign k)
            (unif.cover.assign k i) x := by
          simp only [ShadedTube.shadeClass, Tube.coverClass, Finset.mem_filter]
          exact ⟨⟨hi, by trivial⟩, hxi⟩
        have hpos : (1 : ℕ) ≤ (ShadedTube.shadeClass s V (unif.cover.assign k)
            (unif.cover.assign k i) x).card := Finset.card_pos.2 ⟨i, hmem⟩
        have : (1 : NNReal) ≤ ((ShadedTube.shadeClass s V (unif.cover.assign k)
            (unif.cover.assign k i) x).card : NNReal) := by exact_mod_cast hpos
        calc (1 : NNReal) ≤ _ := this
          _ ≤ ((s.card : NNReal) + 1) * _ := le_mul_of_one_le_left bot_le hC1
      branchingN_le := by
        intro x hx k hk
        simp
      le_branchingN := by
        intro x hx k hk
        simp }

/-- **From a carrier-level hole system to a flat islanded shading.** -/
theorem exists_flatIsland_shading {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {η exscal : ℝ} (hη : 0 < η) {ι : Type*} (s : Finset ι) (hne : s.Nonempty)
    (K : ι → Tube δ E3) (y : ι → E3)
    (hball : ∀ i ∈ s, (K i).carrier ⊆ closedBall 0 1)
    (hinj : ∀ i ∈ s, ∀ j ∈ s, (K i).x = (K j).x → (K i).y = (K j).y → i = j)
    (hisl : ∀ i ∈ s, 0 < volume ((K i).carrier ∩ closedBall (y i) ((δ ^ exscal : NNReal) : ℝ)))
    (hroom : ∀ i ∈ s, ((δ ^ η : NNReal) : ENNReal) * volume (K i).carrier
        ≤ volume ((K i).carrier \ ⋃ j ∈ s, closedBall (y j) (4 * ((δ ^ exscal : NNReal) : ℝ)))) :
    ∃ T : ι → ShadedTube δ E3,
      (∀ i, (T i).toTube = K i) ∧
      (∃ C : NNReal, Nonempty (ShadedTube.ShadedUniformTubeSet s T (Tube.ssfGridLen δ) C)) ∧
      ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) = δ ^ η ∧
      (∀ i ∈ s, volume (T i).shade = ((δ ^ η : NNReal) : ENNReal) * volume (T i).carrier) ∧
      (∀ i ∈ s, ∃ z : E3,
        0 < volume ((T i).shade ∩ closedBall z ((δ ^ exscal : NNReal) : ℝ)) ∧
        volume ((⋃ j ∈ s, (T j).shade) ∩ closedBall z (4 * ((δ ^ exscal : NNReal) : ℝ)))
          < (δ : ENNReal) ^ (3 * η) * volume (ball (0 : E3) (δ : ℝ))) := by
  classical
  set r₁ : ℝ := ((δ ^ exscal : NNReal) : ℝ) with hr₁_def
  have hr₁0 : 0 ≤ r₁ := NNReal.coe_nonneg _
  set H : Set E3 := ⋃ j ∈ s, closedBall (y j) (4 * r₁) with hH_def
  have hHmeas : MeasurableSet H := by
    refine Finset.measurableSet_biUnion s ?_
    intro j _
    exact measurableSet_closedBall
  have hball4H : ∀ i ∈ s, closedBall (y i) (4 * r₁) ⊆ H := by
    intro i hi
    rw [hH_def]
    exact Set.subset_iUnion₂ (s := fun j (_ : j ∈ s) => closedBall (y j) (4 * r₁)) i hi
  have hballH : ∀ i ∈ s, closedBall (y i) r₁ ⊆ H := by
    intro i hi
    exact (closedBall_subset_closedBall (by linarith)).trans (hball4H i hi)
  -- carrier facts
  have hcarmeas : ∀ i, MeasurableSet (K i).carrier := fun i =>
    (K i).toConvexSpaceBody.isCompact.isClosed.measurableSet
  have hcarpos : ∀ i, 0 < volume (K i).carrier := fun i => volume_tube_carrier_pos hδ (K i)
  have hcartop : ∀ i, volume (K i).carrier ≠ ⊤ := fun i =>
    (K i).toConvexSpaceBody.isCompact.measure_lt_top.ne
  -- the mass cap
  set cap : ENNReal := (δ : ENNReal) ^ (3 * η) * volume (ball (0 : E3) (δ : ℝ)) with hcap_def
  have hcappos : 0 < cap := by
    refine ENNReal.mul_pos ?_ ?_
    · exact (ENNReal.rpow_pos (x := (δ : ENNReal)) (by exact_mod_cast hδ) (by simp)).ne'
    · exact (measure_ball_pos volume 0 (by exact_mod_cast hδ)).ne'
  have hcaptop : cap ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by linarith) (by simp))
      measure_ball_lt_top.ne
  -- the sliver size `ε`
  have hntop : (s.card : ENNReal) ≠ ⊤ := by simp
  set d : ENNReal := (s.card : ENNReal) + 1 with hd_def
  have hd0 : d ≠ 0 := by simp [hd_def]
  have hdtop : d ≠ ⊤ := by simp [hd_def]
  set c' : ENNReal := cap / d with hc'_def
  have hc'pos : 0 < c' := ENNReal.div_pos hcappos.ne' hdtop
  have hdc' : d * c' = cap :=
    ENNReal.mul_div_cancel' (fun h => absurd h hd0) (fun h => absurd h hdtop)
  have hc'top : c' ≠ ⊤ := by
    intro h
    rw [hc'_def] at h
    rw [hc'_def, h] at hdc'
    simp [hd0] at hdc'
    exact hcaptop hdc'.symm
  have hnc' : (s.card : ENNReal) * c' < cap := by
    have h1 : (s.card : ENNReal) * c' ≠ ⊤ := ENNReal.mul_ne_top hntop hc'top
    calc (s.card : ENNReal) * c' < (s.card : ENNReal) * c' + c' :=
          ENNReal.lt_add_right h1 hc'pos.ne'
      _ = ((s.card : ENNReal) + 1) * c' := by ring
      _ = cap := hdc'
  set m₀ : ENNReal := s.inf' hne (fun i => volume ((K i).carrier ∩ closedBall (y i) r₁)) with hm₀
  set m₁ : ENNReal :=
    s.inf' hne (fun i => ((δ ^ η : NNReal) : ENNReal) * volume (K i).carrier) with hm₁
  have hm₀pos : 0 < m₀ := by
    rw [hm₀, Finset.lt_inf'_iff]
    exact hisl
  have hm₁pos : 0 < m₁ := by
    rw [hm₁, Finset.lt_inf'_iff]
    intro i hi
    refine ENNReal.mul_pos ?_ (hcarpos i).ne'
    simpa using (NNReal.rpow_pos (p := η) hδ).ne'
  set ε : ENNReal := min c' (min m₀ m₁) with hε_def
  have hεpos : 0 < ε := lt_min hc'pos (lt_min hm₀pos hm₁pos)
  have hεc' : ε ≤ c' := min_le_left _ _
  have hε₀ : ∀ i ∈ s, ε ≤ volume ((K i).carrier ∩ closedBall (y i) r₁) := by
    intro i hi
    exact le_trans (le_trans (min_le_right _ _) (min_le_left _ _)) (Finset.inf'_le _ hi)
  have hε₁ : ∀ i ∈ s, ε ≤ ((δ ^ η : NNReal) : ENNReal) * volume (K i).carrier := by
    intro i hi
    exact le_trans (le_trans (min_le_right _ _) (min_le_right _ _)) (Finset.inf'_le _ hi)
  have hεtop : ε ≠ ⊤ := ne_top_of_le_ne_top hc'top hεc'
  -- the shading of each tube
  have hex : ∀ i : ι, ∃ Sh : Set E3, MeasurableSet Sh ∧ Sh ⊆ (K i).carrier ∧
      (i ∈ s → volume Sh = ((δ ^ η : NNReal) : ENNReal) * volume (K i).carrier) ∧
      (i ∈ s → volume (Sh ∩ H) ≤ ε) ∧
      (i ∈ s → ε ≤ volume (Sh ∩ closedBall (y i) r₁)) := by
    intro i
    by_cases hi : i ∈ s
    · -- the island sliver
      obtain ⟨Ei, hEim, hEisub, hEivol⟩ :=
        exists_subset_volume_eq (A := (K i).carrier ∩ closedBall (y i) r₁)
          ((hcarmeas i).inter measurableSet_closedBall) (R := 1) zero_le_one
          (fun z hz => hball i hi hz.1) (hε₀ i hi)
      -- the main part, outside every hole
      obtain ⟨Si, hSim, hSisub, hSivol⟩ :=
        exists_subset_volume_eq (A := (K i).carrier \ H)
          ((hcarmeas i).diff hHmeas) (R := 1) zero_le_one
          (fun z hz => hball i hi hz.1)
          (m := ((δ ^ η : NNReal) : ENNReal) * volume (K i).carrier - ε)
          (le_trans tsub_le_self (hroom i hi))
      have hdisj : Disjoint Si Ei := by
        refine Set.disjoint_left.2 ?_
        intro z hzS hzE
        exact (hSisub hzS).2 (hballH i hi (hEisub hzE).2)
      refine ⟨Si ∪ Ei, hSim.union hEim, ?_, ?_, ?_, ?_⟩
      · exact Set.union_subset (fun z hz => (hSisub hz).1) (fun z hz => (hEisub hz).1)
      · intro _
        rw [measure_union hdisj hEim, hSivol, hEivol]
        exact tsub_add_cancel_of_le (hε₁ i hi)
      · intro _
        have hsub : (Si ∪ Ei) ∩ H ⊆ Ei := by
          intro z hz
          rcases hz.1 with h | h
          · exact absurd hz.2 (hSisub h).2
          · exact h
        calc volume ((Si ∪ Ei) ∩ H) ≤ volume Ei := measure_mono hsub
          _ = ε := hEivol
      · intro _
        have hsub : Ei ⊆ (Si ∪ Ei) ∩ closedBall (y i) r₁ := by
          intro z hz
          exact ⟨Or.inr hz, (hEisub hz).2⟩
        calc ε = volume Ei := hEivol.symm
          _ ≤ _ := measure_mono hsub
    · exact ⟨∅, MeasurableSet.empty, Set.empty_subset _, fun h => absurd h hi,
        fun h => absurd h hi, fun h => absurd h hi⟩
  choose Sh hShmeas hShsub hShvol hShH hShisl using hex
  -- the shaded family
  set T : ι → ShadedTube δ E3 := fun i =>
    { toTube := K i, shade := Sh i, measurableSet_shade := hShmeas i,
      shade_subset := hShsub i } with hT_def
  refine ⟨T, fun i => rfl, ?_, ?_, ?_, ?_⟩
  · exact exists_shadedUniformTubeSet_of_axes_injOn hδ hδ1 s _ _ hinj
  · -- fullness
    have hsum : ∑ i ∈ s, volume (Sh i)
        = ((δ ^ η : NNReal) : ENNReal) * ∑ i ∈ s, volume (K i).carrier := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i hi => hShvol i hi)
    have hsum0 : (∑ i ∈ s, volume (K i).carrier) ≠ 0 := by
      obtain ⟨i₀, hi₀⟩ := hne
      refine ne_of_gt (lt_of_lt_of_le (hcarpos i₀) ?_)
      exact Finset.single_le_sum (f := fun i => volume (K i).carrier)
        (fun i _ => bot_le) hi₀
    have hsumtop : (∑ i ∈ s, volume (K i).carrier) ≠ ⊤ :=
      by simpa using (ENNReal.sum_ne_top).2 (fun i _ => hcartop i)
    have hfull' : ShadedBody.fullness' s (fun i ↦ (T i).toShadedBody)
        = ((δ ^ η : NNReal) : ENNReal) := by
      show (∑ i ∈ s, volume (Sh i)) / (∑ i ∈ s, volume (K i).carrier) = _
      rw [hsum, ENNReal.mul_div_cancel_right hsum0 hsumtop]
    show (ShadedBody.fullness' s _).toNNReal = _
    rw [hfull']
    simp
  · intro i hi
    exact hShvol i hi
  · intro i hi
    refine ⟨y i, lt_of_lt_of_le hεpos (hShisl i hi), ?_⟩
    have hstep : volume ((⋃ j ∈ s, Sh j) ∩ closedBall (y i) (4 * r₁))
        ≤ (s.card : ENNReal) * ε := by
      have hb : (⋃ j ∈ s, Sh j) ∩ closedBall (y i) (4 * r₁) ⊆ ⋃ j ∈ s, (Sh j ∩ H) := by
        intro z hz
        obtain ⟨j, hj, hzj⟩ := Set.mem_iUnion₂.1 hz.1
        exact Set.mem_iUnion₂.2 ⟨j, hj, hzj, hball4H i hi hz.2⟩
      calc volume ((⋃ j ∈ s, Sh j) ∩ closedBall (y i) (4 * r₁))
          ≤ volume (⋃ j ∈ s, (Sh j ∩ H)) := measure_mono hb
        _ ≤ ∑ j ∈ s, volume (Sh j ∩ H) := measure_biUnion_finset_le _ _
        _ ≤ ∑ _j ∈ s, ε := Finset.sum_le_sum (fun j hj => hShH j hj)
        _ = (s.card : ENNReal) * ε := by
              rw [Finset.sum_const, nsmul_eq_mul]
    refine lt_of_le_of_lt hstep ?_
    exact lt_of_le_of_lt (by gcongr) hnc'


open scoped Classical in
/-- **`exists_setup_caseSideData` is FALSE for any family of carriers that admits a hole
system** — the carrier-level form of
`Kakeya.VeryNotSticky.not_setupCaseSideDataStatement_of_flat_island`.

The hypothesis mentions **no shading at all**.  It asks, for arbitrarily small `δ`, for a finite
family of `δ`-tubes `K` in `B_1` with

* pairwise distinct axes (a normalisation: repeated tubes may be pruned);
* `Δ_max(K) ≤ δ^{-η}` and the `ρ`-count `ρ^{-2-ζ} ≤ |t_ρ|` over `ρ ∈ [δ^{1-exscal}, δ^{exscal}]`
  — verbatim the two *carrier* binders of the target, i.e. GWZ Lemma 9.1's own hypotheses;

together with a **hole system** `y : ι → ℝ³`:

* every member meets its own hole in positive measure,
  `0 < |K i ∩ B̄(y i, r₁)|`, with `r₁ = δ^exscal`;
* no member loses more than a `1 - δ^η` fraction of its carrier to the union of the *enlarged*
  holes, `δ^η |K i| ≤ |K i \ ⋃_j B̄(y j, 4 r₁)|`.

The shading is then constructed by `Kakeya.VeryNotSticky.exists_flatIsland_shading`: a main part
of mass `δ^η|K i| - ε` outside every hole, plus a sliver of mass `ε` inside the member's own
hole, with `ε` small enough that all the slivers together weigh less than the mass floor
`δ^{3η}|B_δ|` that `Kakeya.VeryNotSticky.caseSideData_pieceMass` forces on every piece of the
cover.  The uniformity binder of the frozen pre-F12a statement is supplied free by
`Kakeya.VeryNotSticky.exists_shadedUniformTubeSet_of_axes_injOn`; the live statement's bounded
binder is not, which is why `H` is
`Kakeya.VeryNotSticky.SetupCaseSideDataStatementOld`.

The hole system is a placement statement about `r₁`-balls, with plenty of room: the holes have
total volume `≍ M r₁³` while each member need only avoid the `O(1)`-many it meets, at a cost of
`O(r₁)` of its unit length. -/
theorem not_rigidFullnessField_of_carrier_holes
    {β ζ exscal ϱ η τ τ' : Real} (hβ : 0 < β) (hβ1 : β ≤ 1) (hζ : 0 < ζ) (hexscal : 0 < exscal)
    (hϱ : 0 < ϱ) (hη : 0 < η) (params : CaseParams β ζ exscal ϱ η τ τ')
    (hplankF : PlankFrostmanBudget.{u} β ϱ τ η)
    (hKT : KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β)
    (hF : FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β)
    (hwit : ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∃ (ι : Type u) (s : Finset ι) (K : ι → Tube δ E3) (y : ι → E3),
        s.Nonempty ∧
        (∀ i ∈ s, (K i).carrier ⊆ Metric.closedBall 0 1) ∧
        (∀ i ∈ s, ∀ j ∈ s, (K i).x = (K j).x → (K i).y = (K j).y → i = j) ∧
        maxDensity s (fun i ↦ (K i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η) ∧
        (∀ ρ : NNReal, ρ ∈ Set.Icc (δ ^ (1 - exscal)) (δ ^ exscal) →
          ∃ (κ : Type u) (tρ : Finset κ) (Tρ : κ → Tube ρ E3),
            (tρ : Set κ).Pairwise
              (fun j k ↦ IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) ∧
            (∀ j ∈ tρ, ∃ i ∈ s, (K i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) ∧
            (ρ : ℝ) ^ (-2 - ζ) ≤ (tρ.card : ℝ)) ∧
        (∀ i ∈ s, 0 < volume ((K i).carrier ∩ closedBall (y i) ((δ ^ exscal : NNReal) : ℝ))) ∧
        (∀ i ∈ s, ((δ ^ η : NNReal) : ENNReal) * volume (K i).carrier
          ≤ volume ((K i).carrier \
              ⋃ j ∈ s, closedBall (y j) (4 * ((δ ^ exscal : NNReal) : ℝ)))))
    (H : SetupCaseSideDataStatementOld.{u})
    (hcover : UniformShadingCoverField.{u})
    (w : Kakeya.CoarseKTWindow.{u} β ϱ η exscal) :
    ¬ RigidFullnessField.{u} := by
  refine not_rigidFullnessField_of_flat_island hβ hβ1 hζ hexscal hϱ hη params hplankF
    hKT hF ?_ H hcover w
  have hpos : ∀ᶠ (δ : NNReal) in 𝓝[>] 0, (0 : NNReal) < δ := eventually_mem_nhdsWithin
  have hle1 : ∀ᶠ (δ : NNReal) in 𝓝[>] 0, δ ≤ 1 := by
    refine Filter.Eventually.filter_mono nhdsWithin_le_nhds ?_
    refine Filter.eventually_of_mem (Iio_mem_nhds (by norm_num : (0 : NNReal) < 1)) ?_
    intro x hx
    exact le_of_lt hx
  filter_upwards [hwit, hpos, hle1] with δ hδwit hδ hδ1
  obtain ⟨ι, s, K, y, hne, hball, hinj, hmax, hcount, hisl, hroom⟩ := hδwit
  obtain ⟨T, hTK, huni, hfull, hflat, hisland⟩ :=
    exists_flatIsland_shading hδ hδ1 hη s hne K y hball hinj hisl hroom
  have hbody : ∀ i, (T i).toConvexSpaceBody = (K i).toConvexSpaceBody := by
    intro i
    exact congrArg Tube.toConvexSpaceBody (hTK i)
  have hcarrier : ∀ i, (T i).carrier = (K i).carrier := by
    intro i
    exact congrArg ConvexSpaceBody.carrier (hbody i)
  refine ⟨ι, s, T, ?_, huni, ?_, ?_, ?_, ?_, hisland⟩
  · intro i hi
    rw [hcarrier i]
    exact hball i hi
  · have : (fun i ↦ (T i).toConvexSpaceBody) = fun i ↦ (K i).toConvexSpaceBody :=
      funext hbody
    rw [this]
    exact hmax
  · exact ge_of_eq hfull
  · intro ρ hρ
    obtain ⟨κ, tρ, Tρ, hpw, hused, hcard⟩ := hcount ρ hρ
    refine ⟨κ, tρ, Tρ, hpw, ?_, hcard⟩
    intro j hj
    obtain ⟨i, hi, hij⟩ := hused j hj
    exact ⟨i, hi, by rwa [hbody i]⟩
  · intro i hi
    exact hflat i hi

open scoped Classical in
/-- **`exists_setup_caseSideData` is FALSE for a carrier family with a hole system** — the
original conclusion of `Kakeya.VeryNotSticky.not_rigidFullnessField_of_carrier_holes`, recovered
from the old fullness clause.

This is the same `Kakeya.ThinCase.Refute.statement_of_universal_loc` shape that
`Kakeya.VeryNotSticky.not_setupCaseSideDataStatement_of_flat_island` now carries, and for the
same reason: after `Kakeya.VeryNotSticky.fullness_ge` was repaired to `δ^{2η}` the structure no
longer supplies the rigidity this refutation exploits, so the rigidity is named as a hypothesis
rather than silently lost; likewise the covering of the *uniform* shading, which is distinct from covering the working shading, is the named hypothesis `hcover`.  `hfield` is
false — that is what the repair established — and combining the two merely reproves
`¬ hfield`; the point is the compiled record that a carrier-level hole system suffices to force
it. -/
theorem not_setupCaseSideDataStatement_of_carrier_holes
    {β ζ exscal ϱ η τ τ' : Real} (hβ : 0 < β) (hβ1 : β ≤ 1) (hζ : 0 < ζ) (hexscal : 0 < exscal)
    (hϱ : 0 < ϱ) (hη : 0 < η) (params : CaseParams β ζ exscal ϱ η τ τ')
    (hplankF : PlankFrostmanBudget.{u} β ϱ τ η)
    (hKT : KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β)
    (hF : FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β)
    (hwit : ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∃ (ι : Type u) (s : Finset ι) (K : ι → Tube δ E3) (y : ι → E3),
        s.Nonempty ∧
        (∀ i ∈ s, (K i).carrier ⊆ Metric.closedBall 0 1) ∧
        (∀ i ∈ s, ∀ j ∈ s, (K i).x = (K j).x → (K i).y = (K j).y → i = j) ∧
        maxDensity s (fun i ↦ (K i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η) ∧
        (∀ ρ : NNReal, ρ ∈ Set.Icc (δ ^ (1 - exscal)) (δ ^ exscal) →
          ∃ (κ : Type u) (tρ : Finset κ) (Tρ : κ → Tube ρ E3),
            (tρ : Set κ).Pairwise
              (fun j k ↦ IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) ∧
            (∀ j ∈ tρ, ∃ i ∈ s, (K i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) ∧
            (ρ : ℝ) ^ (-2 - ζ) ≤ (tρ.card : ℝ)) ∧
        (∀ i ∈ s, 0 < volume ((K i).carrier ∩ closedBall (y i) ((δ ^ exscal : NNReal) : ℝ))) ∧
        (∀ i ∈ s, ((δ ^ η : NNReal) : ENNReal) * volume (K i).carrier
          ≤ volume ((K i).carrier \
              ⋃ j ∈ s, closedBall (y j) (4 * ((δ ^ exscal : NNReal) : ℝ)))))
    (hfield : RigidFullnessField.{u})
    (hcover : UniformShadingCoverField.{u})
    (w : Kakeya.CoarseKTWindow.{u} β ϱ η exscal) :
    ¬ SetupCaseSideDataStatementOld.{u} := fun H =>
  absurd hfield (not_rigidFullnessField_of_carrier_holes hβ hβ1 hζ hexscal hϱ hη params hplankF
    hKT hF hwit H hcover w)

end Kakeya.VeryNotSticky

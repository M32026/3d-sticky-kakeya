/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineEccentric
public import Kakeya.StickyKakeya.BallReduction

/-!
# Main Lemma 2, geometric core: the eccentric case, wired

Blueprint: `blueprint/src/GWZAdapted/section9.tex`, "Proof of Main Lemma~\ref{lemmain2}", the
paragraph *"The eccentric case"* (GWZ lines 118--124).
-/

@[expose] public section

open MeasureTheory Metric ConvexSpaceBody ShadedBody
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

section Net

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Translating a set that lies in `B̄(x, r)` by `-x` puts it in `B̄(0, r)`. -/
theorem image_add_neg_subset_closedBall_zero {A : Set E} {x : E} {r : ℝ}
    (h : A ⊆ Metric.closedBall x r) :
    ((fun y => -x + y) '' A) ⊆ Metric.closedBall (0 : E) r := by
  rintro z ⟨y, hy, rfl⟩
  rw [Metric.mem_closedBall, dist_eq_norm, show (-x + y) - 0 = y - x by abel]
  simpa [dist_eq_norm] using Metric.mem_closedBall.mp (h hy)

/-- **A ball assignment at a radius the net controls.**

`Kakeya.StickyKakeya.exists_ball_assignment` places every `δ`-tube of `B̄(0,R)` into a
`B̄(x,1)` for a net point `x`; the radius `1` is baked in and is *too large* for the eccentric
case, whose leaf-ball radius must satisfy `r + 4 ρ ≤ 1`.  This is the same construction with the
achieved radius exposed: a `c`-net of `B̄(0,R)` puts a tube of thickness `ρ` inside
`B̄(x, 1/2 + ρ + c)`, because a tube's carrier lies within `1/2 + ρ` of its core midpoint
(`Tube.carrier_subset_closedBall_midpoint`).  The net is quantified **before** the thickness, so
its cardinality is a `δ`-free constant. -/
theorem exists_tube_ball_net {R c : ℝ} (hR : 0 ≤ R) (hc : 0 < c) :
    ∃ xs : Finset E, xs.Nonempty ∧
      ∀ {ρ : ℝ≥0} (P : Tube ρ E), P.carrier ⊆ Metric.closedBall (0 : E) R →
        ∃ x ∈ xs, P.carrier ⊆ Metric.closedBall x (1 / 2 + (ρ : ℝ) + c) := by
  obtain ⟨xs, hxs_mem, hcover⟩ :=
    Kakeya.closedBall_finite_closedBall_cover (E := E) R hc (0 : E)
  have hne : xs.Nonempty := by
    have h0 : (0 : E) ∈ Metric.closedBall (0 : E) R := by
      rw [Metric.mem_closedBall, dist_self]; exact hR
    obtain ⟨x, hx, -⟩ := Set.mem_iUnion₂.mp (hcover h0)
    exact ⟨x, hx⟩
  refine ⟨xs, hne, ?_⟩
  · intro ρ P hsub
    have hρ0 : (0 : ℝ) ≤ (ρ : ℝ) := ρ.coe_nonneg
    have hmid : midpoint ℝ P.x P.y ∈ P.carrier := by
      rw [P.carrier_eq]
      exact Set.mem_iUnion₂.mpr
        ⟨midpoint ℝ P.x P.y, midpoint_mem_segment (𝕜 := ℝ) P.x P.y,
          Metric.mem_closedBall_self hρ0⟩
    obtain ⟨x, hx, hxmid⟩ := Set.mem_iUnion₂.mp (hcover (hsub hmid))
    refine ⟨x, hx, ?_⟩
    intro p hp
    have h1 : dist p (midpoint ℝ P.x P.y) ≤ 1 / 2 + (ρ : ℝ) :=
      Metric.mem_closedBall.mp (Tube.carrier_subset_closedBall_midpoint (E := E) P hp)
    have h2 : dist (midpoint ℝ P.x P.y) x ≤ c := Metric.mem_closedBall.mp hxmid
    rw [Metric.mem_closedBall]
    calc dist p x ≤ dist p (midpoint ℝ P.x P.y) + dist (midpoint ℝ P.x P.y) x :=
          dist_triangle _ _ _
      _ ≤ (1 / 2 + (ρ : ℝ)) + c := add_le_add h1 h2
      _ = 1 / 2 + (ρ : ℝ) + c := by ring

end Net



section Pigeonhole

/-- **Pigeonhole in a nonnegative weight, over the fibres of a labelling.**

`Kakeya.StickyKakeya.exists_pigeonhole_subfamily` retains a `1/M` share of the *cardinality*;
the eccentric-case seam has to retain a `1/M` share of the *mass*, because the object the seam
discards is a parent and the price of discarding a parent is the mass of its whole leaf class
(`Kakeya.ML2Reduction.sum_le_of_parentMass_heavy`).  This is that statement: some fibre of the
labelling carries at least a `1/#(image)` share of the total weight.  It is a maximum, not an
averaging argument, so it holds verbatim in `ℝ≥0∞` with no finiteness side condition. -/
theorem exists_max_fiber_sum {κ α : Type*} [DecidableEq α] (t : Finset κ) (g : κ → α)
    (w : κ → ℝ≥0∞) :
    ∃ q : Finset κ, q ⊆ t ∧ (∀ k ∈ q, ∀ k' ∈ q, g k = g k') ∧ (t.Nonempty → q.Nonempty) ∧
      ∑ k ∈ t, w k ≤ ((t.image g).card : ℝ≥0∞) * ∑ k ∈ q, w k := by
  classical
  rcases t.eq_empty_or_nonempty with rfl | hne
  · exact ⟨∅, Finset.Subset.refl _, by simp, fun h => absurd h (by simp), by simp⟩
  have hIne : (t.image g).Nonempty := hne.image g
  obtain ⟨x₀, hx₀, hmax⟩ :=
    Finset.exists_max_image (t.image g) (fun x => ∑ k ∈ t.filter (fun k => g k = x), w k) hIne
  refine ⟨t.filter (fun k => g k = x₀), Finset.filter_subset _ _, ?_, ?_, ?_⟩
  · intro k hk k' hk'
    rw [(Finset.mem_filter.mp hk).2, (Finset.mem_filter.mp hk').2]
  · intro _
    obtain ⟨k, hk, hgk⟩ := Finset.mem_image.mp hx₀
    exact ⟨k, Finset.mem_filter.mpr ⟨hk, hgk⟩⟩
  · have hmaps : ∀ k ∈ t, g k ∈ t.image g := fun k hk => Finset.mem_image_of_mem g hk
    calc ∑ k ∈ t, w k
        = ∑ x ∈ t.image g, ∑ k ∈ t.filter (fun k => g k = x), w k :=
          (Finset.sum_fiberwise_of_maps_to hmaps w).symm
      _ ≤ ∑ _x ∈ t.image g, ∑ k ∈ t.filter (fun k => g k = x₀), w k :=
          Finset.sum_le_sum fun x hx => hmax x hx
      _ = ((t.image g).card : ℝ≥0∞) * ∑ k ∈ t.filter (fun k => g k = x₀), w k := by
          rw [Finset.sum_const, nsmul_eq_mul]

end Pigeonhole

section Factoring

/-- **`ConvexSpaceBody.nonempty_factorization.C` is monotone in its cardinality argument.**

The constant is `ofReal (1 + logb 2 card) * ofReal (1 + logb 2 (1/δ)) ^ dim`, and only the first
factor moves with `card`.  Without this, a seam that *discards* objects — as
`Kakeya.ML2Core.exists_plankSeam` does — would have to ask its caller for the factoring-loss
bound at every cardinality below the original one, which is strictly more than
`Kakeya.ML2Reduction.eccentric_of_maxDensityFactoring_crossed` itself asks.  With it, the seam is
free on this side: the caller's obligation is unchanged.  The `card = 0` corner is real, since
`Real.logb 2 0 = 0` rather than `-∞`, and is discharged separately. -/
theorem factorizationC_mono_card {dim m n : ℕ} (h : m ≤ n) (δ : ℝ≥0) :
    ConvexSpaceBody.nonempty_factorization.C dim m δ
      ≤ ConvexSpaceBody.nonempty_factorization.C dim n δ := by
  refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
  have hlog : Real.logb 2 ((m : ℝ) / 1) ≤ Real.logb 2 ((n : ℝ) / 1) := by
    rw [div_one, div_one]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp only [Nat.cast_zero, Real.logb_zero]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · exact Real.logb_nonneg (by norm_num) (by exact_mod_cast hn)
    · exact Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hm) (by exact_mod_cast h)
  linarith

end Factoring

section Translate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Translating both sides of a tube-body containment by a common vector is an equivalence. -/
theorem tube_translate_le_iff {ρ₁ ρ₂ : ℝ≥0} (A : Tube ρ₁ E) (B : Tube ρ₂ E) (v : E) :
    ((A.translate v).toConvexSpaceBody ≤ (B.translate v).toConvexSpaceBody) ↔
      (A.toConvexSpaceBody ≤ B.toConvexSpaceBody) :=
  translate_le_translate_iff v

/-- The carrier of a translated tube. -/
theorem tube_translate_carrier {ρ : ℝ≥0} (T : Tube ρ E) (v : E) :
    (T.translate v).carrier = (fun y => v + y) '' T.carrier := rfl

/-- Undoing a translation: `(T.translate (-v)).translate v = T`.  The mirror of
`Kakeya.StickyKakeya.tube_translate_neg_cancel`, which is what the bounded-overlap clause of
`Tube.IsUniformAtScale` needs, since that clause quantifies over *all* `ρ`-tubes and so has to
be reindexed along `V ↦ V.translate (-v)`. -/
theorem tube_translate_neg_cancel' {ρ : ℝ≥0} (T : Tube ρ E) (v : E) :
    (T.translate (-v)).translate v = T := by
  have := StickyKakeya.tube_translate_neg_cancel (E := E) T (-v)
  rwa [neg_neg] at this

variable [MeasureSpace E]

open Classical in
/-- **A single-scale uniformity structure translates.**

Every clause of GWZ Definition 2.1 is translation equivariant.  The parent tubes are translated
with the leaves; the branching number and the parent index set are unchanged.  The one clause
that is not a pointwise rewrite is `Tube.IsUniformAtScale.boundedOverlap`, which quantifies over
*all* `ρ`-tubes `V`; it is discharged by reading the original clause at `V.translate (-v)`. -/
def translateUniform {ι : Type*} {δ ρ C D : ℝ≥0} {s : Finset ι} {T : ι → Tube δ E}
    (PS : Tube.IsUniformAtScale s T ρ C D) (v : E) :
    Tube.IsUniformAtScale s (fun i => (T i).translate v) ρ C D where
  branchingN := PS.branchingN
  parent := PS.parent
  parentTube := fun j => (PS.parentTube j).translate v
  exists_le_rescale := by
    intro i hi
    obtain ⟨j, hj, hle⟩ := PS.exists_le_rescale hi
    exact ⟨j, hj, (tube_translate_le_iff (T i) (PS.parentTube j) v).mpr hle⟩
  boundedOverlap := by
    intro V
    have hset : (PS.parent.filter fun j => ∃ i ∈ s,
          ((T i).translate v).toConvexSpaceBody
              ≤ ((PS.parentTube j).translate v).toConvexSpaceBody ∧
          ((T i).translate v).toConvexSpaceBody ≤ V.toConvexSpaceBody)
        = (PS.parent.filter fun j => ∃ i ∈ s,
            (T i).toConvexSpaceBody ≤ (PS.parentTube j).toConvexSpaceBody ∧
            (T i).toConvexSpaceBody ≤ (V.translate (-v)).toConvexSpaceBody) := by
      refine Finset.ext fun j => ?_
      simp only [Finset.mem_filter, and_congr_right_iff]
      intro _
      constructor
      · rintro ⟨i, hi, h1, h2⟩
        refine ⟨i, hi, (tube_translate_le_iff (T i) (PS.parentTube j) v).mp h1, ?_⟩
        refine (tube_translate_le_iff (T i) (V.translate (-v)) v).mp ?_
        rwa [tube_translate_neg_cancel' V v]
      · rintro ⟨i, hi, h1, h2⟩
        refine ⟨i, hi, (tube_translate_le_iff (T i) (PS.parentTube j) v).mpr h1, ?_⟩
        have hh := (tube_translate_le_iff (T i) (V.translate (-v)) v).mpr h2
        rwa [tube_translate_neg_cancel' V v] at hh
    rw [hset]
    exact PS.boundedOverlap (V.translate (-v))
  parentTube_injOn := by
    intro a ha b hb hab
    refine PS.parentTube_injOn ha hb ?_
    have h := congrArg (fun (P : Tube ρ E) => P.translate (-v)) hab
    simpa only [StickyKakeya.tube_translate_neg_cancel] using h
  card_filter_le := by
    intro j hj
    have hset : {i ∈ s | ((T i).translate v).toConvexSpaceBody
          ≤ ((PS.parentTube j).translate v).toConvexSpaceBody}
        = {i ∈ s | (T i).toConvexSpaceBody ≤ (PS.parentTube j).toConvexSpaceBody} := by
      refine Finset.ext fun i => ?_
      simp only [Finset.mem_filter, and_congr_right_iff]
      intro _
      exact tube_translate_le_iff (T i) (PS.parentTube j) v
    rw [hset]
    exact PS.card_filter_le hj
  le_mul_card_filter := by
    intro j hj
    have hset : {i ∈ s | ((T i).translate v).toConvexSpaceBody
          ≤ ((PS.parentTube j).translate v).toConvexSpaceBody}
        = {i ∈ s | (T i).toConvexSpaceBody ≤ (PS.parentTube j).toConvexSpaceBody} := by
      refine Finset.ext fun i => ?_
      simp only [Finset.mem_filter, and_congr_right_iff]
      intro _
      exact tube_translate_le_iff (T i) (PS.parentTube j) v
    rw [hset]
    exact PS.le_mul_card_filter hj

end Translate

section Seam

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E]

omit [MeasureSpace E] in
open Classical in
/-- **The plank-scale parent-ball seam** — GWZ Section 9, `\eqref{eqecccase}`'s normalisation, and
the second bite of the `r + 4 ρ ≤ 1` defect.

`Kakeya.ML2Reduction.eccentric_of_maxDensityFactoring_crossed` needs the leaves in `B̄(0, r)` with
`r + 4 ρ ≤ 1`, and `r ≥ 1/2` is forced (a leaf is a unit segment thickened), so a family merely
normalised to `B̄(0,1)` — which is all the rescaled datum of GWZ step 5 supplies — does **not**
satisfy it: at `r = 1` the constraint reads `ρ ≤ 0`.

The repair has the same *shape* as the grid-scale seam (net, pigeonhole, one translation, priced
discard) but is paid in a **different currency**, because the object discarded here is a *parent*,
and the tree already knows the mass cost of discarding a parent: it is
`Kakeya.ML2Reduction.sum_le_of_parentMass_heavy`, at the bounded-overlap constant `D`.  So the
pigeonhole is run in the weight `Kakeya.ML2Reduction.parentMass PS f`
(`Kakeya.ML2Core.exists_max_fiber_sum`) rather than in the cardinality, and **neither
`ML2Shaded.HasDenseShading` nor the two class brackets of GWZ Definition 2.1(iii) is needed**.
The price in the conclusion below is therefore `M · D`, where the grid-scale seam's is
`M · Cu² / lam`.  The two `M`s are cardinalities of different nets, so this records *which*
constants appear, and is **not** a claim that one seam is numerically cheaper than the other.

The radius accounting, at `ρ ≤ 1/16`: the parents lie in `B̄(0, 1 + 4ρ) ⊆ B̄(0,2)`
(`Kakeya.ML2Reduction.parentTube_carrier_subset_closedBall`); a `1/8`-net of `B̄(0,2)` puts each
parent in `B̄(x, 1/2 + ρ + 1/8) ⊆ B̄(x, 3/4)` (`Kakeya.ML2Core.exists_tube_ball_net`); the leaves
of retained parents are inside their parents; and `3/4 + 4 ρ ≤ 1`.  The net cardinality `M` is
quantified **before** `δ`, `ρ` and the family, so it is an absolute constant. -/
theorem exists_plankSeam.{u} :
    ∃ M : ℕ, 0 < M ∧
      ∀ {ι : Type u} {δ ρ C D : ℝ≥0} {s : Finset ι} {T : ι → Tube δ E}
        (PS : Tube.IsUniformAtScale s T ρ C D),
        δ ≤ ρ → 0 < PS.branchingN → 16 * (ρ : ℝ) ≤ 1 →
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
        ∀ f : ι → ℝ≥0∞,
        ∃ (v : E) (p : Finset ι), p ⊆ PS.parent ∧
          (PS.parent.Nonempty → p.Nonempty) ∧
          (∀ i ∈ ML2Reduction.restrictedLeaves PS p,
            ((T i).translate v).carrier ⊆ Metric.closedBall (0 : E) (3 / 4)) ∧
          ∑ i ∈ s, f i
            ≤ (M : ℝ≥0∞) * (D : ℝ≥0∞) * ∑ i ∈ ML2Reduction.restrictedLeaves PS p, f i := by
  classical
  obtain ⟨xs, hxsne, hnet⟩ :=
    exists_tube_ball_net (E := E) (R := 2) (c := 1 / 8) (by norm_num) (by norm_num)
  refine ⟨xs.card, Finset.card_pos.mpr hxsne, ?_⟩
  intro ι δ ρ C D s T PS hδρ hN hρ hleaf f
  have hρ0 : (0 : ℝ) ≤ (ρ : ℝ) := ρ.coe_nonneg
  have hρ1 : 2 * (ρ : ℝ) < 1 := by linarith
  have hpar2 : ∀ j ∈ PS.parent, (PS.parentTube j).carrier ⊆ Metric.closedBall (0 : E) 2 := by
    intro j hj
    refine (ML2Reduction.parentTube_carrier_subset_closedBall PS hρ1
      (fun j' hj' => ML2Reduction.exists_leaf_of_mem_parent PS hN hj') hleaf j hj).trans ?_
    exact Metric.closedBall_subset_closedBall (by linarith)
  let x₀ : E := hxsne.choose
  have hx₀ : x₀ ∈ xs := hxsne.choose_spec
  let g : ι → E := fun j =>
    if h : ∃ x ∈ xs, (PS.parentTube j).carrier ⊆ Metric.closedBall x (1 / 2 + (ρ : ℝ) + 1 / 8)
      then h.choose else x₀
  have hgmem : ∀ j, g j ∈ xs := by
    intro j
    dsimp [g]
    by_cases h : ∃ x ∈ xs, (PS.parentTube j).carrier
        ⊆ Metric.closedBall x (1 / 2 + (ρ : ℝ) + 1 / 8)
    · rw [dif_pos h]
      exact h.choose_spec.1
    · rw [dif_neg h]
      exact hx₀
  have hgball : ∀ j ∈ PS.parent, (PS.parentTube j).carrier
      ⊆ Metric.closedBall (g j) (1 / 2 + (ρ : ℝ) + 1 / 8) := by
    intro j hj
    have hcond : ∃ x ∈ xs, (PS.parentTube j).carrier
        ⊆ Metric.closedBall x (1 / 2 + (ρ : ℝ) + 1 / 8) := hnet (PS.parentTube j) (hpar2 j hj)
    dsimp [g]
    rw [dif_pos hcond]
    exact hcond.choose_spec.2
  obtain ⟨p, hp, hlab, hpne, hmass0⟩ :=
    exists_max_fiber_sum PS.parent g (ML2Reduction.parentMass PS f)
  have himg : ((PS.parent.image g).card : ℝ≥0∞) ≤ (xs.card : ℝ≥0∞) := by
    have : (PS.parent.image g).card ≤ xs.card :=
      Finset.card_le_card (fun x hx => by
        obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hx
        exact hgmem j)
    exact_mod_cast this
  have hheavy : ∑ k ∈ PS.parent, ML2Reduction.parentMass PS f k
      ≤ (xs.card : ℝ≥0∞) * ∑ k ∈ p, ML2Reduction.parentMass PS f k :=
    hmass0.trans (by gcongr)
  have hsum : ∑ i ∈ s, f i
      ≤ (xs.card : ℝ≥0∞) * (D : ℝ≥0∞)
        * ∑ i ∈ ML2Reduction.restrictedLeaves PS p, f i :=
    ML2Reduction.sum_le_of_parentMass_heavy PS hδρ hp f hheavy
  rcases PS.parent.eq_empty_or_nonempty with hemp | hne
  · -- a structure with no parents has no leaves, so every clause is vacuous
    refine ⟨0, p, hp, hpne, ?_, hsum⟩
    have hp0 : p = ∅ := Finset.subset_empty.mp (hemp ▸ hp)
    intro i hi
    rw [hp0] at hi
    obtain ⟨j, hj, -⟩ := (Finset.mem_filter.mp hi).2
    exact absurd hj (by simp)
  · obtain ⟨j₁, hj₁⟩ := hpne hne
    refine ⟨-(g j₁), p, hp, hpne, ?_, hsum⟩
    intro i hi
    obtain ⟨j, hjp, hle⟩ := (Finset.mem_filter.mp hi).2
    have hcar : (T i).carrier ⊆ Metric.closedBall (g j₁) (3 / 4) := by
      have h1 : (T i).carrier ⊆ Metric.closedBall (g j) (1 / 2 + (ρ : ℝ) + 1 / 8) :=
        fun x hx => hgball j (hp hjp) (hle hx)
      rw [hlab j hjp j₁ hj₁] at h1
      exact h1.trans (Metric.closedBall_subset_closedBall (by linarith))
    rw [tube_translate_carrier]
    exact image_add_neg_subset_closedBall_zero hcar

end Seam

section Wiring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Translating a shaded `δ`-tube translates its shaded body.

**Duplicate, deliberately.**  `Kakeya.ml1Boot.shadedTube_translate_toShadedBody`
(`MainLemma1/Rescaling/BallRadius.lean:180`) is the same statement, but `MainLemma1/` is
read-only for this row and must not be imported from `Reduction/`. -/
theorem shadedTube_translate_toShadedBody {δ : ℝ≥0} (S : ShadedTube δ E) (v : E) :
    (S.translate v).toShadedBody = (S.toShadedBody).translate v := rfl

end Wiring

section Wire3

open Classical in
/-- **The eccentric case of GWZ Main Lemma 2, wired to a family normalised only to `B̄(0,1)`.**

Blueprint `section9.tex`, "The eccentric case" (GWZ lines 118--124).  This is
`Kakeya.ML2Reduction.eccentric_of_maxDensityFactoring_crossed` with its **`r + 4 ρ ≤ 1` leaf-ball
hypothesis discharged** from the only normalisation the rescaled datum of step 5 supplies, namely
`r = 1`.  The discharge is `Kakeya.ML2Core.exists_plankSeam`, and the price of it is the single
explicit factor `M · max 1 Cpar` in the conclusion, with `M` an absolute constant (a `1/8`-net of
`B̄(0,2)`) fixed before `β`, `δ`, `ρ` and the family.

What each hypothesis is for:

* `16 ρ ≤ 1` is the seam's threshold.  It is **not** implied by `δ^{1-ε₂} ≤ ρ`, which is a *lower*
  bound on `ρ`, so it is a genuine hypothesis; at the blueprint's `ρ = δ̃^{1-ε₂}` it is eventually
  free precisely when `ε₂ < 1`, which `Kakeya.ML2Spine.IsSpine.eps₂_le_half` grants
  (`Kakeya.ML2Core.exists_threshold_sixteen_plankScale`).  At `ε₂ = 1` the seam is dead:
  `ρ ≥ 1`, and even `2 ρ < 1` fails.
* the factoring-loss hypothesis is asked at `PS.parent.card`, which is **exactly** what
  `Kakeya.ML2Reduction.eccentric_of_maxDensityFactoring_crossed` asks, even though the seam
  discards parents and the factoring therefore runs at `p.card ≤ PS.parent.card`.  The gap is
  closed inside, by `Kakeya.ML2Core.factorizationC_mono_card`; no caller pays for the discard on
  this side.
* the fullness floor is asked for *with the seam's loss already multiplied in*, in `ℝ≥0∞`, which
  is the honest form: the seam's discard costs fullness exactly once, through
  `Kakeya.ML2Reduction.fullness'_le_mul_of_subset_of_sum_shade_le`.
* `Cpar` is raised to `max 1 Cpar` internally (`Tube.IsUniformAtScale.mono`, which moves no
  witness) because the fullness transport has to cancel the loss and therefore needs it nonzero;
  `max 1 Cpar ≤ δ^{-η₀}` still holds, since `1 ≤ 2 ≤ δ^{-η₀}`.

The shaded uniformity `huni` is handed back on the doubly-refined leaf family `q` and on the
*translated* tubes, because `ShadedTube.ShadedUniformTubeSet` has two-sided class brackets and is
not hereditary — that is the crossed theorem's own recorded boundary, and the seam does not move
it.  Everything else — fullness, density, essential distinctness, multiplicity — is stated on the
**original, untranslated** family `(s, T)`. -/
theorem eccentric_of_leafUnitBall.{u} {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hKKT : KatzTaoEstimate (EuclideanSpace ℝ (Fin 3)) β)
    (hKF : FrostmanEstimate (EuclideanSpace ℝ (Fin 3)) β)
    {ε₂ η : ℝ} (hε₂0 : 0 < ε₂) (hε₂1 : ε₂ ≤ 1) (hη : 0 < η) :
    ∃ M : ℕ, 0 < M ∧ ∃ η₀ > (0 : ℝ), ∃ δ₀ > (0 : ℝ≥0), δ₀ ≤ 1 ∧
      ∀ {ι : Type u} (s : Finset ι) {δ : ℝ≥0}, 0 < δ →
        ∀ T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)),
        δ ≤ δ₀ → (2 : ℝ≥0) ≤ δ ^ (-η₀) →
        ∀ ρ Cpar : ℝ≥0, Cpar ≤ δ ^ (-η₀) → (δ : ℝ≥0) ^ (1 - ε₂) ≤ ρ → 16 * (ρ : ℝ) ≤ 1 →
        ∀ PS : Tube.IsUniformAtScale s (fun i => (T i).toTube) ρ Cpar,
          PS.parent.Nonempty → (max 1 Cpar) ^ 2 ≤ PS.branchingN →
          (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
          (s : Set ι).Pairwise
            (fun i j => _root_.IsEssentiallyDistinct (T i).carrier (T j).carrier) →
          ConvexSpaceBody.nonempty_factorization.C 3 PS.parent.card ρ
              * ((max 1 Cpar : ℝ≥0) : ℝ≥0∞) ≤ (δ : ℝ≥0∞) ^ (-(η₀ / 2)) →
          (δ : ℝ≥0∞) ^ (η₀ / 2) * ((M : ℝ≥0∞) * ((max 1 Cpar : ℝ≥0) : ℝ≥0∞))
            ≤ ShadedBody.fullness' s (fun i => (T i).toShadedBody) →
          maxDensity s (fun i => (T i).toConvexSpaceBody) ≤ (δ : ℝ≥0∞) ^ (-(η / ε₂)) →
          ∃ (v : EuclideanSpace ℝ (Fin 3)) (q : Finset ι) (pa pb : ℝ≥0), q ⊆ s ∧
            ((∃ C : ℝ≥0, C ≤ δ ^ (-η₀) ∧
                Nonempty (ShadedTube.ShadedUniformTubeSet q (fun i => (T i).translate v)
                  (Tube.ssfGridLen δ) C)) →
              ML2Reduction.IsEccentric β ε₂ η δ pa pb →
              ShadedBody.multiplicity s (fun i => (T i).toShadedBody)
                ≤ (M : ℝ≥0∞) * ((max 1 Cpar : ℝ≥0) : ℝ≥0∞)
                    * (δ : ℝ≥0∞) ^ (10 * η / ε₂ - η₀ / 2) * (s.card : ℝ≥0∞) ^ β) := by
  classical
  obtain ⟨M, hM, hseam⟩ := exists_plankSeam (E := EuclideanSpace ℝ (Fin 3))
  obtain ⟨η₀, hη₀, δ₀, hδ₀, hδ₀1, hmain⟩ :=
    ML2Reduction.eccentric_of_maxDensityFactoring_crossed hβ0 hβ1 hKKT hKF hε₂0 hε₂1 hη
  refine ⟨M, hM, η₀, hη₀, δ₀, hδ₀, hδ₀1, ?_⟩
  intro ι s δ hδ0 T hδ h2 ρ Cpar hCpar hρlb hρ16 PS hne hbr hleaf hED hloss hfull hΔ
  have hδ1 : δ ≤ 1 := hδ.trans hδ₀1
  have hδne : (δ : ℝ≥0) ≠ 0 := hδ0.ne'
  have hρ0 : (0 : ℝ) ≤ (ρ : ℝ) := ρ.coe_nonneg
  have hδρ : δ ≤ ρ := by
    refine le_trans ?_ hρlb
    have := NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (show (1 : ℝ) - ε₂ ≤ 1 by linarith)
    simpa using this
  -- raise the uniformity constant to `max 1 Cpar`; no witness moves
  have hCpar'le : max 1 Cpar ≤ δ ^ (-η₀) := max_le (one_le_two.trans h2) hCpar
  have hCpar'1 : (1 : ℝ≥0) ≤ max 1 Cpar := le_max_left _ _
  set PS₁ := PS.mono (le_max_right 1 Cpar) (le_max_right 1 Cpar) with hPS₁def
  have hbrN : 0 < PS₁.branchingN :=
    lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one (one_le_pow₀ hCpar'1)) hbr
  -- the seam
  obtain ⟨v, p, hp, hpne, hball34, hmass⟩ :=
    hseam PS₁ hδρ hbrN hρ16 hleaf (fun i => volume (T i).shade)
  set s₁ : Finset ι := ML2Reduction.restrictedLeaves PS₁ p with hs₁def
  have hs₁s : s₁ ⊆ s := ML2Reduction.restrictedLeaves_subset PS₁ p
  set PS₂ := translateUniform (ML2Reduction.restrictParents PS₁ hp) v with hPS₂def
  -- the loss the seam charges: `M · max 1 Cpar`
  have hLne : ((M : ℝ≥0∞) * ((max 1 Cpar : ℝ≥0) : ℝ≥0∞)) ≠ 0 := by
    refine mul_ne_zero ?_ ?_
    · exact_mod_cast hM.ne'
    · simp
  have hLtop : ((M : ℝ≥0∞) * ((max 1 Cpar : ℝ≥0) : ℝ≥0∞)) ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) ENNReal.coe_ne_top
  have hmassE : ∑ i ∈ s, volume ((fun i => (T i).toShadedBody) i).shade
      ≤ ((M : ℝ≥0∞) * ((max 1 Cpar : ℝ≥0) : ℝ≥0∞))
        * ∑ i ∈ s₁, volume ((fun i => (T i).toShadedBody) i).shade := hmass
  -- the fullness floor crosses the seam
  have hfull' : (δ : ℝ≥0∞) ^ (η₀ / 2)
      ≤ ShadedBody.fullness' s₁ (fun i => (T i).toShadedBody) := by
    have hstep := ML2Reduction.fullness'_le_mul_of_subset_of_sum_shade_le hs₁s hmassE
    have hchain : ((M : ℝ≥0∞) * ((max 1 Cpar : ℝ≥0) : ℝ≥0∞)) * (δ : ℝ≥0∞) ^ (η₀ / 2)
        ≤ ((M : ℝ≥0∞) * ((max 1 Cpar : ℝ≥0) : ℝ≥0∞))
          * ShadedBody.fullness' s₁ (fun i => (T i).toShadedBody) := by
      rw [mul_comm ((M : ℝ≥0∞) * ((max 1 Cpar : ℝ≥0) : ℝ≥0∞)) ((δ : ℝ≥0∞) ^ (η₀ / 2))]
      exact hfull.trans hstep
    exact (ENNReal.mul_le_mul_iff_right hLne hLtop).mp hchain
  have hfullN : (δ : ℝ≥0) ^ (η₀ / 2)
      ≤ ShadedBody.fullness s₁ (fun i => (T i).toShadedBody) := by
    have hcoe : ((δ ^ (η₀ / 2) : ℝ≥0) : ℝ≥0∞)
        ≤ ((ShadedBody.fullness s₁ (fun i => (T i).toShadedBody) : ℝ≥0) : ℝ≥0∞) := by
      rw [ENNReal.coe_rpow_of_ne_zero hδne, ShadedBody.coe_fullness]
      exact hfull'
    exact_mod_cast hcoe
  have hfullT : ShadedBody.fullness s₁ (fun i => ((T i).translate v).toShadedBody)
      = ShadedBody.fullness s₁ (fun i => (T i).toShadedBody) := by
    simp only [shadedTube_translate_toShadedBody]
    exact ShadedBody.fullness_translate_const s₁ (fun i => (T i).toShadedBody) v
  -- the density bound crosses for free
  have hΔ₂ : maxDensity s₁ (fun i => ((T i).translate v).toConvexSpaceBody)
      ≤ (δ : ℝ≥0∞) ^ (-(η / ε₂)) := by
    have h1 : maxDensity s₁ (fun i => ((T i).translate v).toConvexSpaceBody)
        = maxDensity s₁ (fun i => (T i).toConvexSpaceBody) :=
      StickyKakeya.maxDensity_tube_translate s₁ (fun i => (T i).toTube) v
    rw [h1]
    exact (Kakeya.maxDensity_mono (fun i => (T i).toConvexSpaceBody) hs₁s).trans hΔ
  -- essential distinctness crosses the translation and the discard
  have hED₂ : (s₁ : Set ι).Pairwise (fun i j =>
      _root_.IsEssentiallyDistinct ((T i).translate v).carrier ((T j).translate v).carrier) := by
    intro i hi j hj hij
    refine (Kakeya.isEssentiallyDistinct_translate (T i).carrier (T j).carrier v).mpr ?_
    exact hED (hs₁s hi) (hs₁s hj) hij
  -- the plank-factoring loss, at the retained parent cardinality
  have hloss₂ : ConvexSpaceBody.nonempty_factorization.C 3 PS₂.parent.card ρ
      * ((max 1 Cpar : ℝ≥0) : ℝ≥0∞) ≤ (δ : ℝ≥0∞) ^ (-(η₀ / 2)) :=
    le_trans (mul_le_mul_left (factorizationC_mono_card (Finset.card_le_card hp) ρ) _) hloss
  have hr34 : (3 : ℝ) / 4 + 4 * (ρ : ℝ) ≤ 1 := by linarith
  have hbr₂ : (max 1 (max 1 Cpar)) ^ 2 ≤ PS₂.branchingN := by
    have hmax : max 1 (max 1 Cpar) = max 1 Cpar := by simp
    rw [hmax]
    exact hbr
  obtain ⟨p₂, hp₂, pa, pb, hp₂ne, hconc⟩ :=
    hmain s₁ hδ0 (fun i => (T i).translate v) hδ h2 ρ (max 1 Cpar) hCpar'le hρlb PS₂
      (hpne hne) hbr₂ (3 / 4) (by norm_num) hr34
      hball34 hED₂ hloss₂ (by rw [hfullT]; exact hfullN) hΔ₂
  refine ⟨v, ML2Reduction.restrictedLeaves PS₂ p₂, pa, pb,
    (ML2Reduction.restrictedLeaves_subset PS₂ p₂).trans hs₁s, ?_⟩
  intro huni hecc
  have hres := hconc huni hecc
  have hmultT : ShadedBody.multiplicity s₁ (fun i => ((T i).translate v).toShadedBody)
      = ShadedBody.multiplicity s₁ (fun i => (T i).toShadedBody) := by
    simp only [shadedTube_translate_toShadedBody]
    exact ShadedBody.multiplicity_translate_const s₁ (fun i => (T i).toShadedBody) v
  rw [hmultT] at hres
  have hcard : (s₁.card : ℝ≥0∞) ≤ (s.card : ℝ≥0∞) := by
    exact_mod_cast Finset.card_le_card hs₁s
  calc ShadedBody.multiplicity s (fun i => (T i).toShadedBody)
      ≤ ((M : ℝ≥0∞) * ((max 1 Cpar : ℝ≥0) : ℝ≥0∞))
          * ShadedBody.multiplicity s₁ (fun i => (T i).toShadedBody) :=
        ML2Reduction.multiplicity_le_mul_of_subset_of_sum_shade_le hs₁s hmassE
    _ ≤ ((M : ℝ≥0∞) * ((max 1 Cpar : ℝ≥0) : ℝ≥0∞))
          * ((δ : ℝ≥0∞) ^ (10 * η / ε₂ - η₀ / 2) * (s₁.card : ℝ≥0∞) ^ β) := by gcongr
    _ ≤ ((M : ℝ≥0∞) * ((max 1 Cpar : ℝ≥0) : ℝ≥0∞))
          * ((δ : ℝ≥0∞) ^ (10 * η / ε₂ - η₀ / 2) * (s.card : ℝ≥0∞) ^ β) := by gcongr
    _ = (M : ℝ≥0∞) * ((max 1 Cpar : ℝ≥0) : ℝ≥0∞)
          * (δ : ℝ≥0∞) ^ (10 * η / ε₂ - η₀ / 2) * (s.card : ℝ≥0∞) ^ β := by ring

/-! ### The seam's threshold at the blueprint's own coarse scale -/

/-- A positive power of a small enough `δ` is below any positive bound.  Elementary, and stated
in `ℝ≥0` because that is where `Kakeya.ML2Reduction.plankScale` lives. -/
theorem exists_threshold_rpow_le {c : ℝ≥0} (hc : 0 < c) {a : ℝ} (ha : 0 < a) :
    ∃ δ₀ : ℝ≥0, 0 < δ₀ ∧ δ₀ ≤ 1 ∧ ∀ δ : ℝ≥0, δ ≤ δ₀ → δ ^ a ≤ c := by
  refine ⟨min 1 (c ^ a⁻¹), lt_min zero_lt_one (NNReal.rpow_pos hc), min_le_left _ _, ?_⟩
  intro δ hδ
  calc δ ^ a ≤ (c ^ a⁻¹) ^ a := NNReal.rpow_le_rpow (hδ.trans (min_le_right _ _)) ha.le
    _ = c := by
        rw [← NNReal.rpow_mul, inv_mul_cancel₀ ha.ne', NNReal.rpow_one]

/-- **The `r + 4 ρ ≤ 1` seam is eventually free at `ρ = δ̃^{1-ε₂}`, and only for `ε₂ < 1`.**

`Kakeya.ML2Core.exists_plankSeam` asks `16 ρ ≤ 1`, which at the blueprint's coarse scale
`ρ = Kakeya.ML2Reduction.plankScale δ ε₂ = δ^{1-ε₂}` is a threshold on `δ` alone — **provided
`ε₂ < 1`**.  `Kakeya.ML2Spine.IsSpine.eps₂_le_half` supplies `ε₂ ≤ 1/2`, so on the spine the
hypothesis is free with room to spare.  At `ε₂ = 1` there is no threshold: `plankScale δ 1 = 1`
and even `2 ρ < 1` fails, so the eccentric case's parent-ball hypothesis is unreachable — that is
a *measured* boundary of the route, not a gap in this file. -/
theorem exists_threshold_sixteen_plankScale {ε₂ : ℝ} (hε₂ : ε₂ < 1) :
    ∃ δ₀ : ℝ≥0, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ δ : ℝ≥0, δ ≤ δ₀ → 16 * ((ML2Reduction.plankScale δ ε₂ : ℝ≥0) : ℝ) ≤ 1 := by
  obtain ⟨δ₀, hδ₀, hδ₀1, hle⟩ :=
    exists_threshold_rpow_le (c := (16 : ℝ≥0)⁻¹) (by norm_num) (a := 1 - ε₂) (by linarith)
  refine ⟨δ₀, hδ₀, hδ₀1, fun δ hδ => ?_⟩
  have h : ((δ ^ (1 - ε₂) : ℝ≥0) : ℝ) ≤ ((16 : ℝ≥0)⁻¹ : ℝ≥0) := by exact_mod_cast hle δ hδ
  rw [ML2Reduction.plankScale]
  push_cast at h ⊢
  linarith

open Classical in
/-- **The eccentric case at the blueprint's own coarse scale `ρ = δ̃^{1-ε₂}`, leaf-ball seam
included.**

`Kakeya.ML2Core.eccentric_of_leafUnitBall` instantiated at `ρ := Kakeya.ML2Reduction.plankScale
δ ε₂`, where its coarse-scale hypothesis `δ^{1-ε₂} ≤ ρ` is `le_rfl` and its seam threshold
`16 ρ ≤ 1` has been absorbed into `δ₀`.  This is the statement that the seam of
`Kakeya.ML2Core.exists_plankSeam` is applicable at the one scale GWZ Section 9 uses it, and it is
the entry point the estimate should call: **nothing about the parents, and no leaf ball smaller
than `B̄(0,1)`, has to be supplied.** -/
theorem eccentric_atPlankScale.{u} {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hKKT : KatzTaoEstimate (EuclideanSpace ℝ (Fin 3)) β)
    (hKF : FrostmanEstimate (EuclideanSpace ℝ (Fin 3)) β)
    {ε₂ η : ℝ} (hε₂0 : 0 < ε₂) (hε₂1 : ε₂ < 1) (hη : 0 < η) :
    ∃ M : ℕ, 0 < M ∧ ∃ η₀ > (0 : ℝ), ∃ δ₀ > (0 : ℝ≥0), δ₀ ≤ 1 ∧
      ∀ {ι : Type u} (s : Finset ι) {δ : ℝ≥0}, 0 < δ →
        ∀ T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)),
        δ ≤ δ₀ → (2 : ℝ≥0) ≤ δ ^ (-η₀) →
        ∀ Cpar : ℝ≥0, Cpar ≤ δ ^ (-η₀) →
        ∀ PS : Tube.IsUniformAtScale s (fun i => (T i).toTube)
          (ML2Reduction.plankScale δ ε₂) Cpar,
          PS.parent.Nonempty → (max 1 Cpar) ^ 2 ≤ PS.branchingN →
          (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
          (s : Set ι).Pairwise
            (fun i j => _root_.IsEssentiallyDistinct (T i).carrier (T j).carrier) →
          ConvexSpaceBody.nonempty_factorization.C 3 PS.parent.card
                (ML2Reduction.plankScale δ ε₂) * ((max 1 Cpar : ℝ≥0) : ℝ≥0∞)
              ≤ (δ : ℝ≥0∞) ^ (-(η₀ / 2)) →
          (δ : ℝ≥0∞) ^ (η₀ / 2) * ((M : ℝ≥0∞) * ((max 1 Cpar : ℝ≥0) : ℝ≥0∞))
            ≤ ShadedBody.fullness' s (fun i => (T i).toShadedBody) →
          maxDensity s (fun i => (T i).toConvexSpaceBody) ≤ (δ : ℝ≥0∞) ^ (-(η / ε₂)) →
          ∃ (v : EuclideanSpace ℝ (Fin 3)) (q : Finset ι) (pa pb : ℝ≥0), q ⊆ s ∧
            ((∃ C : ℝ≥0, C ≤ δ ^ (-η₀) ∧
                Nonempty (ShadedTube.ShadedUniformTubeSet q (fun i => (T i).translate v)
                  (Tube.ssfGridLen δ) C)) →
              ML2Reduction.IsEccentric β ε₂ η δ pa pb →
              ShadedBody.multiplicity s (fun i => (T i).toShadedBody)
                ≤ (M : ℝ≥0∞) * ((max 1 Cpar : ℝ≥0) : ℝ≥0∞)
                    * (δ : ℝ≥0∞) ^ (10 * η / ε₂ - η₀ / 2) * (s.card : ℝ≥0∞) ^ β) := by
  obtain ⟨M, hM, η₀, hη₀, δ₀, hδ₀, hδ₀1, hmain⟩ :=
    eccentric_of_leafUnitBall.{u} hβ0 hβ1 hKKT hKF hε₂0 hε₂1.le hη
  obtain ⟨δ₁, hδ₁, hδ₁1, hthr⟩ := exists_threshold_sixteen_plankScale hε₂1
  refine ⟨M, hM, η₀, hη₀, min δ₀ δ₁, lt_min hδ₀ hδ₁, le_trans (min_le_left _ _) hδ₀1, ?_⟩
  intro ι s δ hδ0 T hδ h2 Cpar hCpar PS hne hbr hleaf hED hloss hfull hΔ
  exact hmain s hδ0 T (hδ.trans (min_le_left _ _)) h2 (ML2Reduction.plankScale δ ε₂) Cpar hCpar
    le_rfl (hthr δ (hδ.trans (min_le_right _ _))) PS hne hbr hleaf hED hloss hfull hΔ

end Wire3

end Kakeya.ML2Core

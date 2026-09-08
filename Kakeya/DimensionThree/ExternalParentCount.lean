/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.TubeParentPacking
public import Kakeya.DimensionThree.BoundedOverlapCount

/-!
# Counting the parents of an external parent system

`Kakeya.exists_externalParentSystem_of_four_mul_le` builds, with **no essential distinctness
input**, an `Kakeya.ExternalParentSystem q T ρ parentOverlapConst` whenever `4 * δ ≤ ρ`.  That
object carries a factorisation of the fine family through coarse `ρ`-tubes, but no bound on how
many coarse tubes there are.  This file supplies the missing count, still ED-free:

`|parents| ≤ parentOverlapConst · parentCount.C · ρ ^ (-5)`.

## The mismatch with `Tube.HasBoundedOverlap`

The two bounded-overlap conditions in play are *not* the same, in two independent ways.

* **Test radius.** `Tube.HasBoundedOverlap s V t Vρ Co` quantifies over test tubes `W : Tube ρ E`,
  at the *same* radius as the parents.  `Kakeya.ExternalParentSystem.boundedOverlapThroughLeaves`
  quantifies over test tubes of radius `8 * ρ`.  This direction is harmless: `8 * ρ` is the larger
  test tube, so the `8 * ρ` statement is the stronger one and specialises to radius `ρ` through
  `Tube.le_rescale`.
* **The "through" clause.** `Tube.HasBoundedOverlap` counts a parent `k` when *some* leaf lies in
  both `Vρ k` and `W`; `boundedOverlapThroughLeaves` counts `k` when some leaf **assigned to `k`**
  lies in `W`.  By `Kakeya.ExternalParentSystem.leaf_le_parent`, `assign i = k` implies
  `T i ≤ parentTube k`, so the parent system's filter set is *contained* in the
  `Tube.HasBoundedOverlap` filter set.  The bound therefore transfers in the wrong direction, and
  an external parent system does **not** in general satisfy `Tube.HasBoundedOverlap`: a parent may
  contain leaves that were assigned elsewhere, and nothing in the structure limits how many
  parents share such an unassigned leaf.

So `Kakeya.ml1Boot.card_parents_le_of_hasBoundedOverlap` cannot be applied off the shelf.  What
*can* be reused is its proof, which only ever consults the overlap hypothesis at a designated leaf
per parent.  `Kakeya.ml1Boot.card_le_of_designatedLeaf_overlap` below is that argument, restated
against a designated-leaf map `w : κ → ι`; it is strictly weaker in hypothesis than
`Kakeya.ml1Boot.card_parents_le_of_hasBoundedOverlap` and gives the same `ρ ^ (-5)`.

## Why the exponent is `-5` and not `-6`

The obvious route, `Kakeya.ExternalParentSystem.card_occupiedParents_le`, costs `ρ ^ (-6)`: its
constant `Kakeya.tubeParamPackingConstOf N = (4N+1)^3 * (250N^3+250)` is applied at `N ≍ ρ⁻¹`, and
the second factor is the deliberately non-sharp direction count of
`Kakeya.card_le_of_projective_separated_in_cap`, whose exponent is `Module.finrank ℝ E = 3` rather
than the sharp `2` of a cap in `S²`.  That route is therefore unusable here.

The net route is sharp.  `Kakeya.ml1Boot.exists_dirPos_net` is built from
`Kakeya.ml1Boot.card_le_of_unit_separated`, which *is* the sharp `ρ ^ (-2)` sphere count, times the
`ρ ^ (-3)` midpoint count of `Kakeya.ml1Boot.card_le_of_ball_separated`; `5 = 2 + 3`.

## Discarding the unoccupied parents

`Kakeya.ExternalParentSystem.parents` may contain parents owning no leaf, and those are invisible
to `boundedOverlapThroughLeaves`, hence uncountable by any leaf-mediated argument.  They are also
useless: `Kakeya.ExternalParentSystem.restrictOccupied` deletes them, preserving every field, and
the count is stated for the restricted system.
-/

@[expose] public section

open MeasureTheory Metric

open scoped ENNReal NNReal

namespace Kakeya.ml1Boot

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

open Classical in
/-- **Counting parents from a designated leaf per parent.**

If every parent `k ∈ t` carries a designated `σ`-tube `V (w k)` with carrier in `B̄(0,1)`, and no
`ρ`-tube contains the designated tubes of more than `Co` parents, then

`|t| ≤ Co · parentCount.C · ρ ^ (-5)`.

This is the covering argument of `Kakeya.ml1Boot.card_parents_le_of_hasBoundedOverlap` with its
hypothesis weakened to what that proof actually uses: there the leaf under a parent is produced by
`choose!` from the parenthood hypothesis and the overlap hypothesis is consulted only at the net
tube covering that one leaf.  Here the leaf is given as data instead, and the overlap hypothesis
is correspondingly only about designated leaves.  No essential distinctness, and no containment of
the designated leaf in its own parent, is required. -/
theorem card_le_of_designatedLeaf_overlap [Nontrivial E]
    (hdim : Module.finrank ℝ E = 3)
    {ι κ : Type*} {σ ρ : NNReal} (hσ : 0 < σ) (hρ1 : ρ ≤ 1) (hσρ : 2 * σ ≤ ρ)
    {s : Finset ι} {V : ι → Tube σ E} {t : Finset κ} {Co : NNReal}
    (w : κ → ι) (hw : ∀ k ∈ t, w k ∈ s)
    (hball : ∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 1)
    (hoverlap : ∀ W : Tube ρ E,
      ((t.filter fun k => (V (w k)).toConvexSpaceBody ≤ W.toConvexSpaceBody).card : NNReal) ≤ Co) :
    (t.card : ℝ≥0∞) ≤ (Co : ℝ≥0∞) * (parentCount.C : ℝ≥0∞) * (ρ : ℝ≥0∞) ^ (-5 : ℝ) := by
  classical
  haveI : ProperSpace E := by infer_instance
  have hρ : 0 < ρ := lt_of_lt_of_le (by positivity) hσρ
  have hσhalf : (σ : ℝ) ≤ (ρ : ℝ) / 2 := by
    have h2 : (2 : ℝ) * (σ : ℝ) ≤ (ρ : ℝ) := by
      exact NNReal.coe_le_coe.mpr hσρ
    linarith
  obtain ⟨S, hSunit, hScard, hScover⟩ := exists_dirPos_net hdim hρ hρ1
  obtain ⟨x0, hx0⟩ : ∃ x : E, x ≠ 0 := exists_ne (0 : E)
  let e : E := ‖x0‖⁻¹ • x0
  have he : ‖e‖ = 1 := by
    exact norm_smul_inv_norm hx0
  let uv : E × E → E := fun q => if ‖q.1‖ = 1 then q.1 else e
  have huv : ∀ q, ‖uv q‖ = 1 := by
    intro q
    by_cases h : ‖q.1‖ = 1
    · simp [uv, h]
    · simpa [uv, h] using he
  let Wt : E × E → Tube ρ E := fun q => Tube.ofMidpointDirection ρ q.2 (uv q) (huv q)
  have hWdir : ∀ q, (Wt q).direction = uv q := by
    intro q
    simp [Wt, Tube.direction]
    module
  have hWmid : ∀ q, (Wt q).midpoint = q.2 := by
    intro q
    simp [Wt, Tube.midpoint]
    module
  have hcov : ∀ k : κ, ∀ hk : k ∈ t, ∃ q ∈ S,
      ‖(V (w k)).direction - q.1‖ ≤ (ρ : ℝ) / 16 ∧
      ‖(V (w k)).midpoint - q.2‖ ≤ (ρ : ℝ) / 16 := by
    intro k hk
    exact hScover ((V (w k)).direction) ((V (w k)).midpoint)
      ((V (w k)).norm_direction)
      (Tube.norm_midpoint_le_of_subset_ball hσ (V (w k)) (hball (w k) (hw k hk)))
  let g : κ → E × E := fun k => if hk : k ∈ t then Classical.choose (hcov k hk) else (e, (0 : E))
  have g_mem : ∀ k : κ, ∀ hk : k ∈ t, g k ∈ S := by
    intro k hk
    have hspec := Classical.choose_spec (hcov k hk)
    simpa [g, hk] using hspec.1
  have g_dir : ∀ k : κ, ∀ hk : k ∈ t, ‖(V (w k)).direction - (g k).1‖ ≤ (ρ : ℝ) / 16 := by
    intro k hk
    have hspec := Classical.choose_spec (hcov k hk)
    simpa [g, hk] using hspec.2.1
  have g_mid : ∀ k : κ, ∀ hk : k ∈ t, ‖(V (w k)).midpoint - (g k).2‖ ≤ (ρ : ℝ) / 16 := by
    intro k hk
    have hspec := Classical.choose_spec (hcov k hk)
    simpa [g, hk] using hspec.2.2
  have hin : ∀ k : κ, ∀ hk : k ∈ t, (V (w k)).toConvexSpaceBody ≤
      (Wt (g k)).toConvexSpaceBody := by
    intro k hk
    have hgdir : (Wt (g k)).direction = (g k).1 := by
      rw [hWdir]
      simp [uv, hSunit (g k) (g_mem k hk)]
    have hgmid : (Wt (g k)).midpoint = (g k).2 := by
      rw [hWmid]
    exact Tube.tube_carrier_subset_of_close (V (w k)) (Wt (g k)) (ε_dir := (ρ : ℝ) / 16)
      (ε_pos := (ρ : ℝ) / 16)
      (by
        rw [hgdir]
        exact g_dir k hk)
      (by
        rw [hgmid]
        exact g_mid k hk)
      (by
        have hρ' : (0 : ℝ) < (ρ : ℝ) := by exact_mod_cast hρ
        nlinarith)
  have hfib : ∀ q ∈ S, ((t.filter (fun k => g k = q)).card : ℝ≥0∞) ≤ (Co : ℝ≥0∞) := by
    intro q hq
    have hsub : t.filter (fun k => g k = q) ⊆
        t.filter (fun k => (V (w k)).toConvexSpaceBody ≤ (Wt q).toConvexSpaceBody) := by
      intro k hk
      rw [Finset.mem_filter] at hk ⊢
      rcases hk with ⟨hk, hgq⟩
      refine ⟨hk, ?_⟩
      have htmp := hin k hk
      rw [hgq] at htmp
      exact htmp
    have hcard_le : (t.filter (fun k => g k = q)).card ≤
        (t.filter (fun k => (V (w k)).toConvexSpaceBody ≤ (Wt q).toConvexSpaceBody)).card :=
      Finset.card_le_card hsub
    have hNN : ((t.filter (fun k => g k = q)).card : NNReal) ≤ Co := by
      exact le_trans (by exact_mod_cast hcard_le) (hoverlap (Wt q))
    exact_mod_cast hNN
  have Hmaps : (t : Set κ).MapsTo g S := fun k hk => g_mem k hk
  have hsumNat : t.card = ∑ q ∈ S, (t.filter (fun k => g k = q)).card :=
    Finset.card_eq_sum_card_fiberwise Hmaps
  have hsum : (t.card : ℝ≥0∞) ≤ (S.card : ℝ≥0∞) * (Co : ℝ≥0∞) := by
    calc
      (t.card : ℝ≥0∞) = (∑ q ∈ S, (t.filter (fun k => g k = q)).card : ℝ≥0∞) := by
        exact_mod_cast hsumNat
      _ = ∑ q ∈ S, ((t.filter (fun k => g k = q)).card : ℝ≥0∞) := by
        norm_cast
      _ ≤ ∑ q ∈ S, (Co : ℝ≥0∞) := by
        exact Finset.sum_le_sum fun q hq => hfib q hq
      _ = (S.card : ℝ≥0∞) * (Co : ℝ≥0∞) := by
        rw [Finset.sum_const, nsmul_eq_mul]
  calc
    (t.card : ℝ≥0∞) ≤ (S.card : ℝ≥0∞) * (Co : ℝ≥0∞) := hsum
    _ ≤ (parentCount.C : ℝ≥0∞) * (ρ : ℝ≥0∞)⁻¹ ^ 5 * (Co : ℝ≥0∞) := by
      exact mul_le_mul' hScard (le_refl _)
    _ = (Co : ℝ≥0∞) * (parentCount.C : ℝ≥0∞) * (ρ : ℝ≥0∞) ^ (-5 : ℝ) := by
      rw [← coe_rpow_neg_five ρ]
      ac_rfl

end Kakeya.ml1Boot

namespace Kakeya

open Classical in
/-- The parents of an external parent system that actually own a leaf.

The unoccupied parents carry no information: no leaf is assigned to them, so they are invisible to
`Kakeya.ExternalParentSystem.boundedOverlapThroughLeaves` and cannot be counted. -/
noncomputable def ExternalParentSystem.occupiedParents {ι : Type*} {q : Finset ι} {δ ρ Cu : ℝ≥0}
    {T : ι → Tube δ (EuclideanSpace ℝ (Fin 3))} (PS : ExternalParentSystem q T ρ Cu) :
    Finset PS.Parent :=
  PS.parents.filter fun k => ∃ i ∈ q, PS.assign i = k

/-- Occupied parents are parents. -/
theorem ExternalParentSystem.occupiedParents_subset {ι : Type*} {q : Finset ι} {δ ρ Cu : ℝ≥0}
    {T : ι → Tube δ (EuclideanSpace ℝ (Fin 3))} (PS : ExternalParentSystem q T ρ Cu) :
    PS.occupiedParents ⊆ PS.parents := by
  classical
  simp only [ExternalParentSystem.occupiedParents]
  exact Finset.filter_subset _ _

/-- Every leaf is assigned to an *occupied* parent — itself being the witness. -/
theorem ExternalParentSystem.assign_mem_occupiedParents {ι : Type*} {q : Finset ι} {δ ρ Cu : ℝ≥0}
    {T : ι → Tube δ (EuclideanSpace ℝ (Fin 3))} (PS : ExternalParentSystem q T ρ Cu) :
    ∀ i ∈ q, PS.assign i ∈ PS.occupiedParents := by
  classical
  intro i hi
  simp only [ExternalParentSystem.occupiedParents, Finset.mem_filter]
  exact ⟨PS.assign_mem i hi, i, hi, rfl⟩

open Classical in
/-- Leaf-mediated bounded overlap survives restriction to the occupied parents, the filter set
only shrinking. -/
theorem ExternalParentSystem.boundedOverlapThroughLeaves_occupiedParents {ι : Type*}
    {q : Finset ι} {δ ρ Cu : ℝ≥0} {T : ι → Tube δ (EuclideanSpace ℝ (Fin 3))}
    (PS : ExternalParentSystem q T ρ Cu) :
    ∀ V : Tube (8 * ρ) (EuclideanSpace ℝ (Fin 3)),
      (((PS.occupiedParents.filter fun k => ∃ i ∈ q, PS.assign i = k ∧
          (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody)).card : ℝ≥0) ≤ Cu := by
  classical
  intro V
  refine le_trans ?_ (PS.boundedOverlapThroughLeaves V)
  have hsub : (PS.occupiedParents.filter fun k => ∃ i ∈ q, PS.assign i = k ∧
        (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody)
      ⊆ (PS.parents.filter fun k => ∃ i ∈ q, PS.assign i = k ∧
        (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody) := by
    intro k hk
    simp only [Finset.mem_filter] at hk ⊢
    exact ⟨PS.occupiedParents_subset hk.1, hk.2⟩
  exact_mod_cast Finset.card_le_card hsub

/-- **The external parent system with its unoccupied parents deleted.**

Every field is inherited; only `Kakeya.ExternalParentSystem.parents` shrinks, to
`Kakeya.ExternalParentSystem.occupiedParents`. -/
noncomputable def ExternalParentSystem.restrictOccupied {ι : Type*} {q : Finset ι} {δ ρ Cu : ℝ≥0}
    {T : ι → Tube δ (EuclideanSpace ℝ (Fin 3))} (PS : ExternalParentSystem q T ρ Cu) :
    ExternalParentSystem q T ρ Cu where
  Parent := PS.Parent
  parents := PS.occupiedParents
  parentTube := PS.parentTube
  assign := PS.assign
  assign_mem := PS.assign_mem_occupiedParents
  leaf_le_parent := PS.leaf_le_parent
  boundedOverlapThroughLeaves := PS.boundedOverlapThroughLeaves_occupiedParents

/-- The parents of the restricted system are exactly the occupied parents. -/
@[simp]
theorem ExternalParentSystem.parents_restrictOccupied {ι : Type*} {q : Finset ι} {δ ρ Cu : ℝ≥0}
    {T : ι → Tube δ (EuclideanSpace ℝ (Fin 3))} (PS : ExternalParentSystem q T ρ Cu) :
    PS.restrictOccupied.parents = PS.occupiedParents := rfl

/-- **The occupied parents of an external parent system are `O(ρ ^ (-5))` in number.**

Purely leaf-mediated, hence entirely free of essential distinctness: each occupied parent is
represented by one leaf assigned to it, the `ρ`-net of
`Kakeya.ml1Boot.exists_dirPos_net` covers that leaf by one of `parentCount.C · ρ ^ (-5)` tubes, and
`Kakeya.ExternalParentSystem.boundedOverlapThroughLeaves` — applied to the net tube rescaled to
radius `8 * ρ` — bounds each fibre by `Cu`.

The `8 * ρ` rescaling is the harmless half of the mismatch with `Tube.HasBoundedOverlap`; the
other half, that the parent system only controls *assigned* leaves, is exactly why
`Kakeya.ml1Boot.card_le_of_designatedLeaf_overlap` is used here in place of
`Kakeya.ml1Boot.card_parents_le_of_hasBoundedOverlap`. -/
theorem ExternalParentSystem.card_occupiedParents_le_rpow {ι : Type*} {q : Finset ι}
    {δ ρ Cu : ℝ≥0} {T : ι → Tube δ (EuclideanSpace ℝ (Fin 3))}
    (PS : ExternalParentSystem q T ρ Cu) (hδ0 : 0 < δ) (hδρ : 2 * δ ≤ ρ) (hρ1 : ρ ≤ 1)
    (hball : ∀ i ∈ q, (T i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    ((PS.occupiedParents.card : ℝ≥0∞)) ≤
      (Cu : ℝ≥0∞) * (ml1Boot.parentCount.C : ℝ≥0∞) * (ρ : ℝ≥0∞) ^ (-5 : ℝ) := by
  classical
  have hocc : ∀ k ∈ PS.occupiedParents, ∃ i, i ∈ q ∧ PS.assign i = k := by
    intro k hk
    simp only [ExternalParentSystem.occupiedParents, Finset.mem_filter] at hk
    obtain ⟨_, i, hi, hik⟩ := hk
    exact ⟨i, hi, hik⟩
  rcases PS.occupiedParents.eq_empty_or_nonempty with hε | hne
  · simp [hε]
  · haveI : Nonempty ι := by
      obtain ⟨i₀, hi₀, _⟩ := hocc (Classical.choose hne) (Classical.choose_spec hne)
      exact ⟨i₀⟩
    choose! w hwq hwk using hocc
    have hoverlap : ∀ W : Tube ρ (EuclideanSpace ℝ (Fin 3)),
        ((PS.occupiedParents.filter fun k : PS.Parent =>
          (T (w k)).toConvexSpaceBody ≤ W.toConvexSpaceBody).card : ℝ≥0) ≤ Cu := by
      intro W
      have hρ_le : ρ ≤ 8 * ρ := by
        calc
          ρ = (1 : ℝ≥0) * ρ := by rw [one_mul]
          _ ≤ 8 * ρ := mul_le_mul_of_nonneg_right (by norm_num : (1 : ℝ≥0) ≤ 8)
            (by positivity : (0 : ℝ≥0) ≤ ρ)
      have hle :
          (PS.occupiedParents.filter fun k : PS.Parent =>
            (T (w k)).toConvexSpaceBody ≤ W.toConvexSpaceBody)
            ⊆ PS.parents.filter fun k : PS.Parent => ∃ i ∈ q, PS.assign i = k ∧
              (T i).toConvexSpaceBody ≤ (W.rescale (8 * ρ)).toConvexSpaceBody := by
        intro k hk
        simp only [Finset.mem_filter] at hk ⊢
        rcases hk with ⟨hkocc, hkW⟩
        constructor
        · exact PS.occupiedParents_subset hkocc
        · refine ⟨w k, hwq k hkocc, hwk k hkocc, ?_⟩
          exact le_trans hkW (W.le_rescale hρ_le)
      have hcard :
          (PS.occupiedParents.filter fun k : PS.Parent =>
            (T (w k)).toConvexSpaceBody ≤ W.toConvexSpaceBody).card
            ≤ (PS.parents.filter fun k : PS.Parent => ∃ i ∈ q, PS.assign i = k ∧
              (T i).toConvexSpaceBody ≤ (W.rescale (8 * ρ)).toConvexSpaceBody).card :=
        Finset.card_le_card hle
      exact le_trans (Nat.cast_le.mpr hcard) (PS.boundedOverlapThroughLeaves (W.rescale (8 * ρ)))
    exact ml1Boot.card_le_of_designatedLeaf_overlap
      (E := EuclideanSpace ℝ (Fin 3)) (finrank_euclideanSpace_fin)
      (σ := δ) (ρ := ρ) (hσ := hδ0) (hρ1 := hρ1) (hσρ := hδρ)
      (s := q) (V := T) (t := PS.occupiedParents) (Co := Cu)
      (w := w) (hw := hwq) (hball := hball) (hoverlap := hoverlap)

/-- The absolute constant of `Kakeya.exists_externalParentSystem_card_le`: the ED-free overlap
constant of the construction times the `ρ ^ (-5)` net constant. -/
noncomputable def externalParentCountConst : ℝ≥0 :=
  parentOverlapConst * ml1Boot.parentCount.C

/-- **An external parent system with an `O(ρ ^ (-5))` parent count, built with no essential
distinctness input.**

For `4 * δ ≤ ρ ≤ 1` and a fine `δ`-tube family in the closed unit ball, there is a family of
coarse `ρ`-tubes, an assignment of each fine leaf to a coarse tube containing it, leaf-mediated
bounded overlap by the absolute constant `Kakeya.parentOverlapConst`, and at most
`externalParentCountConst · ρ ^ (-5)` coarse tubes.

Every hypothesis is a scale inequality or a localisation; in particular the fine family is *not*
assumed pairwise essentially distinct, which is what makes this usable for the node families of a
hierarchy.  The `4 * δ ≤ ρ` slack is what
`Kakeya.exists_externalParentSystem_of_four_mul_le` needs; the near regime `ρ < 4 * δ` is the one
that genuinely consumes essential distinctness and is deliberately excluded. -/
theorem exists_externalParentSystem_card_le
    {ι : Type*} {δ ρ : ℝ≥0} (hδ0 : 0 < δ) (hδρ : 4 * δ ≤ ρ) (hρ1 : ρ ≤ 1)
    (q : Finset ι) (T : ι → Tube δ (EuclideanSpace ℝ (Fin 3)))
    (hball : ∀ i ∈ q, (T i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    ∃ PS : ExternalParentSystem q T ρ parentOverlapConst,
      (PS.parents.card : ℝ≥0∞) ≤
        (externalParentCountConst : ℝ≥0∞) * (ρ : ℝ≥0∞) ^ (-5 : ℝ) := by
  obtain ⟨PS⟩ := exists_externalParentSystem_of_four_mul_le hδ0 hδρ q T hball
  refine ⟨PS.restrictOccupied, ?_⟩
  have h2δρ : 2 * δ ≤ ρ := le_trans (by gcongr; norm_num) hδρ
  have hcard := PS.card_occupiedParents_le_rpow hδ0 h2δρ hρ1 hball
  rw [ExternalParentSystem.parents_restrictOccupied]
  rw [externalParentCountConst, ENNReal.coe_mul]
  exact hcard

end Kakeya

end

import MyLeanRepo.Kakeya.Assouad.Subunit.HairbrushStatements
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic

/-!
# Frostman fiber size bounds and small-fiber removal

Given a partition of a tube family `G` into fibers, each contained in a slab
of volume `≤ C_const * θ`, apply the Frostman slab Wolff bound to derive:

1. Upper bound on each fiber size: `|fiber j| ≤ C_const * θ * δ^{-inputEta} * |G|`
2. Lower bound on fiber count: `N ≥ δ^{inputEta} / (C_const * θ)`
3. Small-fiber removal: discard fibers below threshold `t = δ^outputEta * |G| / N`.
   The remaining `M` fibers satisfy:
   - total remaining `≥ (1 - δ^outputEta) * |G|`
   - coarse count `θ * M ≥ (1 - δ^outputEta) * δ^{inputEta} / C_const`

The balanced-cardinality condition is handled separately by `DyadicBalancing`.
-/

noncomputable section

open MeasureTheory Set Finset

attribute [local instance] Classical.propDecidable

namespace Kakeya.Assouad

section FrostmanFiberSize

variable {δ inputEta outputEta theta C_const : ℝ}
variable {G : Kakeya.TubeFamily δ}
variable {N : ℕ} (fiber : Fin N → Kakeya.TubeFamily δ)
variable (slab : Fin N → Kakeya.Slab)

/-- Each fiber's cardinality is bounded by the Frostman slab estimate. -/
lemma frostman_fiber_size_bound
    (hδ : 0 < δ) (h_inputEta_nonneg : 0 ≤ inputEta)
    (hC_pos : 0 < C_const) (htheta_pos : 0 < theta)
    (hFrost : Kakeya.FrostmanSlabWolffBound G (Real.rpow δ (-inputEta)))
    (h_contained : ∀ j, ∀ T ∈ fiber j, T.carrier ⊆ (slab j).carrier)
    (h_vol : ∀ j, volume (slab j).carrier ≤ ENNReal.ofReal (C_const * theta))
    (hG_nonempty : G.Nonempty)
    (h_fiber_subset : ∀ j, fiber j ⊆ G) :
    ∀ j : Fin N, (fiber j).enncard ≤
      ENNReal.ofReal (C_const * theta * Real.rpow δ (-inputEta)) * G.enncard := by
  intro j
  let S_j : Set Point3 := (slab j).carrier
  have h1 : fiber j ⊆ G.filter fun T => T.carrier ⊆ S_j := by
    intro T hT
    exact Finset.mem_filter.mpr ⟨h_fiber_subset j hT, h_contained j T hT⟩
  have h_card : (fiber j).card ≤ (G.filter fun T => T.carrier ⊆ S_j).card :=
    Finset.card_le_card h1
  have h2 : (fiber j).enncard ≤ G.containedCount S_j := by
    have h_eq : G.containedCount S_j = ((G.filter fun T => T.carrier ⊆ S_j).card : ENNReal) := by rfl
    have h_enncard : (fiber j).enncard = ((fiber j).card : ENNReal) := by
      simp [Kakeya.TubeFamily.enncard]
    rw [h_enncard, h_eq]
    exact Nat.cast_le.mpr h_card
  have h4 := hFrost (slab j)
  have h5 : volume S_j ≤ ENNReal.ofReal (C_const * theta) := h_vol j
  have h6 : G.containedCount S_j ≤
      ENNReal.ofReal (Real.rpow δ (-inputEta)) * volume S_j * G.enncard := h4
  have h7 : G.containedCount S_j ≤
      ENNReal.ofReal (Real.rpow δ (-inputEta)) * ENNReal.ofReal (C_const * theta) * G.enncard := by
    calc G.containedCount S_j
      ≤ ENNReal.ofReal (Real.rpow δ (-inputEta)) * volume S_j * G.enncard := h6
    _ ≤ ENNReal.ofReal (Real.rpow δ (-inputEta)) * ENNReal.ofReal (C_const * theta) * G.enncard := by
        gcongr
  have h_pos1 : 0 ≤ Real.rpow δ (-inputEta) := Real.rpow_nonneg hδ.le _
  have h_pos2 : 0 ≤ C_const * theta := by positivity
  have h_mul : ENNReal.ofReal (Real.rpow δ (-inputEta)) * ENNReal.ofReal (C_const * theta) =
      ENNReal.ofReal (Real.rpow δ (-inputEta) * (C_const * theta)) := by
    exact Eq.symm (ENNReal.ofReal_mul h_pos1)
  have h_comm : Real.rpow δ (-inputEta) * (C_const * theta) =
      C_const * theta * Real.rpow δ (-inputEta) := by ring
  rw [h_mul, h_comm] at h7
  exact h2.trans h7

/-- Real-valued version of the fiber size bound. -/
lemma frostman_fiber_size_bound_real
    (hδ : 0 < δ) (h_inputEta_nonneg : 0 ≤ inputEta)
    (hC_pos : 0 < C_const) (htheta_pos : 0 < theta)
    (hFrost : Kakeya.FrostmanSlabWolffBound G (Real.rpow δ (-inputEta)))
    (h_contained : ∀ j, ∀ T ∈ fiber j, T.carrier ⊆ (slab j).carrier)
    (h_vol : ∀ j, volume (slab j).carrier ≤ ENNReal.ofReal (C_const * theta))
    (hG_nonempty : G.Nonempty)
    (h_fiber_subset : ∀ j, fiber j ⊆ G) :
    ∀ j : Fin N, ((fiber j).card : ℝ) ≤
      C_const * theta * Real.rpow δ (-inputEta) * (G.card : ℝ) := by
  intro j
  set X : ℝ := C_const * theta * Real.rpow δ (-inputEta) * (G.card : ℝ) with hX_def
  have hX_nonneg : 0 ≤ X := by
    dsimp only [X]
    have h1 : 0 ≤ C_const * theta := by positivity
    have h2 : 0 ≤ Real.rpow δ (-inputEta) := Real.rpow_nonneg hδ.le _
    have h3 : 0 ≤ (G.card : ℝ) := by positivity
    positivity
  have h_enn := frostman_fiber_size_bound fiber slab hδ h_inputEta_nonneg hC_pos htheta_pos
    hFrost h_contained h_vol hG_nonempty h_fiber_subset j
  have hG : G.enncard = ENNReal.ofReal (G.card : ℝ) := by
    simp [Kakeya.TubeFamily.enncard] <;> norm_cast
  have h_posC : 0 ≤ C_const * theta * Real.rpow δ (-inputEta) := by
    have h1 : 0 ≤ C_const * theta := by positivity
    have h2 : 0 ≤ Real.rpow δ (-inputEta) := Real.rpow_nonneg hδ.le _
    exact mul_nonneg h1 h2
  have h10 : ENNReal.ofReal (C_const * theta * Real.rpow δ (-inputEta)) * G.enncard =
      ENNReal.ofReal X := by
    rw [hG]
    have h : ENNReal.ofReal (C_const * theta * Real.rpow δ (-inputEta)) * ENNReal.ofReal (G.card : ℝ) =
        ENNReal.ofReal ((C_const * theta * Real.rpow δ (-inputEta)) * (G.card : ℝ)) := by
      exact Eq.symm (ENNReal.ofReal_mul h_posC)
    rw [h, hX_def]
  rw [h10] at h_enn
  have h9 : ((fiber j).card : ENNReal) ≤ ENNReal.ofReal X := h_enn
  have h_top1 : ((fiber j).card : ENNReal) ≠ ⊤ := by simp
  have h_top2 : ENNReal.ofReal X ≠ ⊤ := by simp
  have h9' : ((fiber j).card : ENNReal).toReal ≤ (ENNReal.ofReal X).toReal :=
    (ENNReal.toReal_le_toReal h_top1 h_top2).mpr h9
  have h11 : ((fiber j).card : ENNReal).toReal = ((fiber j).card : ℝ) := by simp
  have h12 : (ENNReal.ofReal X).toReal = X := ENNReal.toReal_ofReal hX_nonneg
  rw [h11, h12] at h9'
  exact h9'

/-- If the fibers form a disjoint partition of `G`, then the number of fibers
is at least `δ^{inputEta} / (C_const * θ)`. -/
lemma fiber_count_lower
    (hδ : 0 < δ) (h_inputEta_nonneg : 0 ≤ inputEta)
    (hC_pos : 0 < C_const) (htheta_pos : 0 < theta)
    (hFrost : Kakeya.FrostmanSlabWolffBound G (Real.rpow δ (-inputEta)))
    (h_contained : ∀ j, ∀ T ∈ fiber j, T.carrier ⊆ (slab j).carrier)
    (h_vol : ∀ j, volume (slab j).carrier ≤ ENNReal.ofReal (C_const * theta))
    (hG_nonempty : G.Nonempty)
    (h_fiber_subset : ∀ j, fiber j ⊆ G)
    (h_union : Finset.biUnion (Finset.univ : Finset (Fin N)) fiber = G)
    (h_disjoint : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin N))) fiber) :
    (N : ENNReal) ≥ ENNReal.ofReal (Real.rpow δ inputEta / (C_const * theta)) := by
  have h_size := frostman_fiber_size_bound fiber slab hδ h_inputEta_nonneg hC_pos htheta_pos
    hFrost h_contained h_vol hG_nonempty h_fiber_subset
  let C_enn : ENNReal := ENNReal.ofReal (C_const * theta * Real.rpow δ (-inputEta))
  have hC_pos' : C_enn ≠ 0 := by
    simp [C_enn, hC_pos, htheta_pos] <;> positivity
  have hC_top : C_enn ≠ ⊤ := by simp [C_enn]
  have h_sum_enn : (Finset.biUnion (Finset.univ : Finset (Fin N)) fiber).card =
      ∑ j : Fin N, (fiber j).card := Finset.card_biUnion h_disjoint
  have h_sum : G.enncard = ∑ j : Fin N, (fiber j).enncard := by
    have h1 : G.card = ∑ j : Fin N, (fiber j).card := by
      rw [← h_sum_enn, h_union]
    have h2 : G.enncard = (G.card : ENNReal) := by
      simp [Kakeya.TubeFamily.enncard]
    have h3 : (∑ j : Fin N, (fiber j).enncard) = (∑ j : Fin N, (fiber j).card : ENNReal) := by
      simp [Kakeya.TubeFamily.enncard] <;> rfl
    rw [h2, h3]
    exact_mod_cast h1
  have h9 : G.enncard ≤ (N : ENNReal) * (C_enn * G.enncard) := by
    calc G.enncard
      = ∑ j : Fin N, (fiber j).enncard := h_sum
    _ ≤ ∑ j : Fin N, (C_enn * G.enncard) := by
        apply Finset.sum_le_sum; intro i _; exact h_size i
    _ = (N : ENNReal) * (C_enn * G.enncard) := by
        simp [Finset.sum_const, mul_assoc] <;> ring
  have hG_ne_zero : G.enncard ≠ 0 := by
    simpa [Kakeya.TubeFamily.enncard] using hG_nonempty.card_pos.ne'
  have hG_top : G.enncard ≠ ⊤ := by
    simp [Kakeya.TubeFamily.enncard]
  have h10 : (1 : ENNReal) ≤ (N : ENNReal) * C_enn := by
    have h9' : G.enncard ≤ G.enncard * ((N : ENNReal) * C_enn) := by
      have h_comm : (N : ENNReal) * (C_enn * G.enncard) = G.enncard * ((N : ENNReal) * C_enn) := by
        simp [mul_assoc, mul_comm] <;> ring
      rw [h_comm] at h9
      exact h9
    have h11 : G.enncard * (1 : ENNReal) ≤ G.enncard * ((N : ENNReal) * C_enn) := by
      have h_one : G.enncard * (1 : ENNReal) = G.enncard := by simp
      rw [h_one]
      exact h9'
    exact (ENNReal.mul_le_mul_iff_right hG_ne_zero hG_top).mp h11
  have h10' : (1 : ENNReal) ≤ C_enn * (N : ENNReal) := by
    have h_comm : C_enn * (N : ENNReal) = (N : ENNReal) * C_enn := by
      rw [mul_comm]
    rw [h_comm]
    exact h10
  have h13 : C_enn⁻¹ ≤ (N : ENNReal) := by
    have h14 : C_enn⁻¹ * (1 : ENNReal) ≤ (N : ENNReal) := by
      rw [ENNReal.inv_mul_le_iff hC_pos' hC_top]
      exact h10'
    simpa using h14
  have h_pos_val : 0 < C_const * theta * Real.rpow δ (-inputEta) := by
    have h1 : 0 < C_const * theta := mul_pos hC_pos htheta_pos
    have h2 : 0 < Real.rpow δ (-inputEta) := Real.rpow_pos_of_pos hδ _
    exact mul_pos h1 h2
  have h15 : C_enn⁻¹ = ENNReal.ofReal ((C_const * theta * Real.rpow δ (-inputEta))⁻¹) := by
    exact Eq.symm (ENNReal.ofReal_inv_of_pos h_pos_val)
  rw [h15] at h13
  have h_rpow_neg' : Real.rpow δ (-inputEta) = (Real.rpow δ inputEta)⁻¹ :=
    Real.rpow_neg hδ.le inputEta
  have h16 : (C_const * theta * Real.rpow δ (-inputEta))⁻¹ =
      Real.rpow δ inputEta / (C_const * theta) := by
    have h17 : (C_const * theta * Real.rpow δ (-inputEta))⁻¹ =
        (Real.rpow δ (-inputEta))⁻¹ / (C_const * theta) := by
      field_simp [hC_pos.ne', htheta_pos.ne'] <;> ring
    rw [h17]
    have h18 : (Real.rpow δ (-inputEta))⁻¹ = Real.rpow δ inputEta := by
      rw [h_rpow_neg']
      have h19 : 0 < Real.rpow δ inputEta := Real.rpow_pos_of_pos hδ _
      field_simp [h19.ne']
    rw [h18] <;> ring
  rw [h16] at h13
  exact h13

/-- Remove fibers whose cardinality is below threshold `t`.

The remaining `M` fibers satisfy:
- total remaining `≥ (1 - δ^outputEta) * |G|`
- coarse count: `θ * M ≥ (1 - δ^outputEta) * δ^{inputEta} / C_const`
-/
lemma small_fiber_removal
    (hδ : 0 < δ) (hδ_le1 : δ ≤ 1)
    (h_inputEta_nonneg : 0 ≤ inputEta) (h_outputEta_pos : 0 < outputEta)
    (hC_pos : 0 < C_const) (htheta_pos : 0 < theta)
    (hFrost : Kakeya.FrostmanSlabWolffBound G (Real.rpow δ (-inputEta)))
    (h_contained : ∀ j, ∀ T ∈ fiber j, T.carrier ⊆ (slab j).carrier)
    (h_vol : ∀ j, volume (slab j).carrier ≤ ENNReal.ofReal (C_const * theta))
    (hG_nonempty : G.Nonempty)
    (h_fiber_subset : ∀ j, fiber j ⊆ G)
    (h_union : Finset.biUnion (Finset.univ : Finset (Fin N)) fiber = G)
    (h_disjoint : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin N))) fiber)
    (hN_pos : 0 < N)
    (t : ℝ) (ht_pos : 0 ≤ t)
    (ht_def : t = Real.rpow δ outputEta * (G.card : ℝ) / (N : ℝ)) :
    ∃ (big : Finset (Fin N)),
      (∀ j ∈ big, t ≤ (fiber j).card) ∧
      ((G.card : ℝ) - (∑ j ∈ big, ((fiber j).card : ℝ)) ≤ (N : ℝ) * t) ∧
      ((1 - Real.rpow δ outputEta) * (G.card : ℝ) ≤ (∑ j ∈ big, ((fiber j).card : ℝ))) ∧
      ENNReal.ofReal theta * (big.card : ENNReal) ≥
        ENNReal.ofReal ((1 - Real.rpow δ outputEta) * Real.rpow δ inputEta / C_const) := by
  let big : Finset (Fin N) := Finset.univ.filter fun j => t ≤ (fiber j).card
  let small : Finset (Fin N) := Finset.univ \ big
  have h_disj' : Disjoint big small := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    exact (Finset.mem_sdiff.mp hx2).2 hx1
  have h_univ' : big ∪ small = Finset.univ := by
    ext x
    simp [big, small] <;> tauto
  have h_sum_card : ∑ j : Fin N, (fiber j).card = G.card := by
    have h : (Finset.biUnion (Finset.univ : Finset (Fin N)) fiber).card =
        ∑ j : Fin N, (fiber j).card := Finset.card_biUnion h_disjoint
    rw [← h, h_union]
  have h_sum_split : (∑ j ∈ big, (fiber j).card) + (∑ j ∈ small, (fiber j).card) = G.card := by
    have h : ∑ j : Fin N, (fiber j).card = (∑ j ∈ big, (fiber j).card) + (∑ j ∈ small, (fiber j).card) := by
      rw [← Finset.sum_union h_disj', h_univ'] <;> rfl
    rw [h] at h_sum_card
    exact h_sum_card
  have h_sum_split' : (∑ j ∈ big, ((fiber j).card : ℝ)) + (∑ j ∈ small, ((fiber j).card : ℝ)) = (G.card : ℝ) := by
    exact_mod_cast h_sum_split
  have h2 : ∀ j ∈ small, ((fiber j).card : ℝ) < t := by
    intro j hj
    have h_j_not_big : j ∉ big := (Finset.mem_sdiff.mp hj).2
    have h : ¬(t ≤ (fiber j).card) := by
      simpa [big, Finset.mem_filter, Finset.mem_univ j] using h_j_not_big
    exact lt_of_not_ge h
  have h3 : (∑ j ∈ small, ((fiber j).card : ℝ)) ≤ (small.card : ℝ) * t := by
    have h4 : ∀ j ∈ small, ((fiber j).card : ℝ) ≤ t := by
      intro j hj; exact le_of_lt (h2 j hj)
    calc (∑ j ∈ small, ((fiber j).card : ℝ))
      ≤ ∑ j ∈ small, t := Finset.sum_le_sum h4
    _ = (small.card : ℝ) * t := by
      rw [Finset.sum_const] <;> ring
  have h51 : small.card ≤ (Finset.univ : Finset (Fin N)).card := Finset.card_le_card (Finset.subset_univ small)
  have h52 : (Finset.univ : Finset (Fin N)).card = N := by simp
  have h5 : (small.card : ℝ) ≤ (N : ℝ) := by
    rw [h52] at h51
    exact_mod_cast h51
  have h6 : (small.card : ℝ) * t ≤ (N : ℝ) * t := by
    gcongr <;> exact ht_pos
  have h4 : (∑ j ∈ small, ((fiber j).card : ℝ)) ≤ (N : ℝ) * t := h3.trans h6
  have h5' : (G.card : ℝ) - (∑ j ∈ big, ((fiber j).card : ℝ)) ≤ (N : ℝ) * t := by
    linarith [h_sum_split', h4]
  have h7 : (N : ℝ) * t = Real.rpow δ outputEta * (G.card : ℝ) := by
    rw [ht_def] <;> field_simp [hN_pos.ne'] <;> ring
  have h6' : (1 - Real.rpow δ outputEta) * (G.card : ℝ) ≤ (∑ j ∈ big, ((fiber j).card : ℝ)) := by
    have h8 : (∑ j ∈ small, ((fiber j).card : ℝ)) ≤ Real.rpow δ outputEta * (G.card : ℝ) := by
      calc (∑ j ∈ small, ((fiber j).card : ℝ))
        ≤ (N : ℝ) * t := h4
      _ = Real.rpow δ outputEta * (G.card : ℝ) := h7
    linarith [h_sum_split', h8]
  have h_size_real : ∀ j : Fin N, ((fiber j).card : ℝ) ≤
      C_const * theta * Real.rpow δ (-inputEta) * (G.card : ℝ) :=
    frostman_fiber_size_bound_real fiber slab hδ h_inputEta_nonneg hC_pos htheta_pos
      hFrost h_contained h_vol hG_nonempty h_fiber_subset
  have hG_card_pos : 0 < (G.card : ℝ) := by exact_mod_cast hG_nonempty.card_pos
  set Y : ℝ := C_const * theta * Real.rpow δ (-inputEta) * (G.card : ℝ) with hY_def
  have hY_pos : 0 < Y := by
    dsimp only [Y]
    have h1 : 0 < C_const * theta := mul_pos hC_pos htheta_pos
    have h2 : 0 < Real.rpow δ (-inputEta) := Real.rpow_pos_of_pos hδ _
    have h3 : 0 < (G.card : ℝ) := by exact_mod_cast hG_nonempty.card_pos
    positivity
  have h_coarse1 : (big.card : ℝ) * Y ≥ (∑ j ∈ big, ((fiber j).card : ℝ)) := by
    calc (big.card : ℝ) * Y
      = ∑ j ∈ big, Y := by rw [Finset.sum_const] <;> ring
    _ ≥ ∑ j ∈ big, ((fiber j).card : ℝ) := by
        apply Finset.sum_le_sum
        intro j _
        exact h_size_real j
  have h_coarse2 : (big.card : ℝ) * Y ≥ (1 - Real.rpow δ outputEta) * (G.card : ℝ) := by
    calc (big.card : ℝ) * Y
      ≥ (∑ j ∈ big, ((fiber j).card : ℝ)) := h_coarse1
    _ ≥ (1 - Real.rpow δ outputEta) * (G.card : ℝ) := by exact_mod_cast h6'
  have h_coarse3 : (big.card : ℝ) ≥
      (1 - Real.rpow δ outputEta) * (G.card : ℝ) / Y := by
    calc (big.card : ℝ)
      = ((big.card : ℝ) * Y) / Y := by field_simp [hY_pos.ne'] <;> ring
    _ ≥ ((1 - Real.rpow δ outputEta) * (G.card : ℝ)) / Y := by gcongr
  have h_rpow_neg : Real.rpow δ (-inputEta) = (Real.rpow δ inputEta)⁻¹ :=
    Real.rpow_neg hδ.le inputEta
  have h_rpow_mul : Real.rpow δ (-inputEta) * Real.rpow δ inputEta = 1 := by
    rw [h_rpow_neg]
    have h_pos : 0 < Real.rpow δ inputEta := Real.rpow_pos_of_pos hδ _
    field_simp [h_pos.ne']
  have h_simp : (1 - Real.rpow δ outputEta) * (G.card : ℝ) / Y =
      (1 - Real.rpow δ outputEta) * Real.rpow δ inputEta / (C_const * theta) := by
    rw [hY_def]
    set D : ℝ := C_const * theta * Real.rpow δ (-inputEta) * (G.card : ℝ) with hD_def
    have hD_ne_zero : D ≠ 0 := by positivity
    have h_eq : ((1 - Real.rpow δ outputEta) * Real.rpow δ inputEta / (C_const * theta)) * D =
        (1 - Real.rpow δ outputEta) * (G.card : ℝ) := by
      rw [hD_def]
      have h : ((1 - Real.rpow δ outputEta) * Real.rpow δ inputEta / (C_const * theta)) *
          (C_const * theta * Real.rpow δ (-inputEta) * (G.card : ℝ)) =
          (1 - Real.rpow δ outputEta) * (Real.rpow δ inputEta * Real.rpow δ (-inputEta)) * (G.card : ℝ) := by
        field_simp [hC_pos.ne', htheta_pos.ne'] <;> ring
      rw [h]
      have h2 : Real.rpow δ inputEta * Real.rpow δ (-inputEta) = 1 := by
        rw [mul_comm, h_rpow_mul]
      rw [h2] <;> ring
    exact (div_eq_iff hD_ne_zero).mpr h_eq.symm
  have h_coarse4 : (big.card : ℝ) ≥
      (1 - Real.rpow δ outputEta) * Real.rpow δ inputEta / (C_const * theta) := by
    rw [h_simp] at h_coarse3
    exact h_coarse3
  have h_coarse5 : (big.card : ℝ) * theta ≥
      (1 - Real.rpow δ outputEta) * Real.rpow δ inputEta / C_const := by
    have h : (big.card : ℝ) ≥
        (1 - Real.rpow δ outputEta) * Real.rpow δ inputEta / (C_const * theta) := h_coarse4
    have h5 : (big.card : ℝ) * theta ≥
        ((1 - Real.rpow δ outputEta) * Real.rpow δ inputEta / (C_const * theta)) * theta := by
      gcongr <;> linarith
    have h6 : ((1 - Real.rpow δ outputEta) * Real.rpow δ inputEta / (C_const * theta)) * theta =
        (1 - Real.rpow δ outputEta) * Real.rpow δ inputEta / C_const := by
      field_simp [hC_pos.ne', htheta_pos.ne'] <;> ring
    rw [h6] at h5
    exact h5
  have h_pos2 : 0 ≤ (1 - Real.rpow δ outputEta) * Real.rpow δ inputEta / C_const := by
    have h1 : 0 ≤ 1 - Real.rpow δ outputEta := by
      have h2 : Real.rpow δ outputEta ≤ 1 := Real.rpow_le_one hδ.le hδ_le1 h_outputEta_pos.le
      linarith
    have h3 : 0 ≤ Real.rpow δ inputEta := Real.rpow_nonneg hδ.le _
    positivity
  have htheta_nonneg : 0 ≤ theta := by linarith
  have h_coarse6 : (1 - Real.rpow δ outputEta) * Real.rpow δ inputEta / C_const ≤
      theta * (big.card : ℝ) := by
    have h_comm : (big.card : ℝ) * theta = theta * (big.card : ℝ) := by ring
    rw [h_comm] at h_coarse5
    exact h_coarse5
  have h_card_cast : (big.card : ENNReal) = ENNReal.ofReal (big.card : ℝ) := by
    simp
  have h_mul : ENNReal.ofReal theta * (big.card : ENNReal) =
      ENNReal.ofReal (theta * (big.card : ℝ)) := by
    rw [h_card_cast]
    rw [← ENNReal.ofReal_mul htheta_nonneg]
    <;> rfl
  have h_last : ENNReal.ofReal theta * (big.card : ENNReal) ≥
      ENNReal.ofReal ((1 - Real.rpow δ outputEta) * Real.rpow δ inputEta / C_const) := by
    rw [h_mul]
    exact ENNReal.ofReal_le_ofReal h_coarse6
  have h1 : ∀ j ∈ big, t ≤ (fiber j).card := by
    intro j hj
    exact (Finset.mem_filter.mp hj).2
  exact ⟨big, h1, h5', h6', h_last⟩

end FrostmanFiberSize

end Kakeya.Assouad

import MyLeanRepo.Kakeya.Assouad.Subunit.HairbrushSelfContainedLeaves
import MyLeanRepo.Kakeya.Assouad.ConstantAbsorption
import MyLeanRepo.Kakeya.Assouad.Subunit.AsymptoticHelper
import MyLeanRepo.Kakeya.Assouad.TubeVolumeScaling
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-!
# Helper lemmas for slab group balancing

This module contains the low-density discard bound and other combinatorial
helpers used by `hairbrush_slab_group_balancing`.

## Main results

* `low_density_discard_bound`: groups below the density floor contribute at
  most half the total mass when the input exponent gap is positive.
-/

noncomputable section

open Finset BigOperators

namespace Kakeya.Assouad

/--
Low-density discard bound.

Given `δ^inputExponent * F.enncard * V ≤ totalMass` and
`∑ cards_j ≤ 1000000 * F.enncard`, for sufficiently small δ the total mass
of groups with `mass_j < δ^densityFloor * cards_j * V` is at most `totalMass / 2`.

The gap `inputExponent < densityFloor` lets the constant 2000000 be absorbed
by the power difference.
-/
lemma low_density_discard_bound
    (inputExponent densityFloor : ℝ)
    (_hinput_pos : 0 < inputExponent)
    (hgap : inputExponent < densityFloor) :
    ∃ (delta₀ : ℝ), 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ (δ : ℝ), 0 < δ → δ ≤ delta₀ →
      ∀ (N : ℕ) (F_enncard V totalMass : ENNReal)
        (cards : Fin N → ENNReal) (masses : Fin N → ENNReal),
        (∑ j : Fin N, cards j ≤ 1000000 * F_enncard) →
        (Kakeya.realRpowENN δ inputExponent * F_enncard * V ≤ totalMass) →
        let S_low := Finset.univ.filter (fun j : Fin N =>
          masses j < Kakeya.realRpowENN δ densityFloor * cards j * V)
        ∑ j ∈ S_low, masses j ≤ totalMass / 2 := by
  have hgap_pos : 0 < densityFloor - inputExponent := by linarith
  rcases exists_delta_realRpowENN_bound (2000000 : ENNReal)
      (by norm_num) hgap_pos with
    ⟨delta₀, hdelta₀_pos, hdelta₀_one, h_absorb⟩
  refine ⟨delta₀, hdelta₀_pos, hdelta₀_one, ?_⟩
  intro δ hδ_pos hδ_le N F_enncard V totalMass cards masses h_cards h_input
  let S_low := Finset.univ.filter (fun j : Fin N =>
    masses j < Kakeya.realRpowENN δ densityFloor * cards j * V)
  set X : ENNReal := (1000000 : ENNReal) * Kakeya.realRpowENN δ densityFloor *
      F_enncard * V with hX_def
  have h1 : (2000000 : ENNReal) * Kakeya.realRpowENN δ densityFloor ≤
      Kakeya.realRpowENN δ inputExponent := by
    have h_absorb' : (2000000 : ENNReal) ≤
        Kakeya.realRpowENN δ (-(densityFloor - inputExponent)) :=
      h_absorb δ hδ_pos hδ_le
    have h_mul : Kakeya.realRpowENN δ (-(densityFloor - inputExponent)) *
        Kakeya.realRpowENN δ densityFloor =
        Kakeya.realRpowENN δ inputExponent := by
      rw [Subunit.realRpowENN_mul hδ_pos]
      have h_exp : (-(densityFloor - inputExponent)) + densityFloor = inputExponent := by ring
      rw [h_exp]
    calc
      (2000000 : ENNReal) * Kakeya.realRpowENN δ densityFloor
        ≤ Kakeya.realRpowENN δ (-(densityFloor - inputExponent)) *
            Kakeya.realRpowENN δ densityFloor := by gcongr
      _ = Kakeya.realRpowENN δ inputExponent := h_mul
  have h2 : (2 : ENNReal) * X ≤ totalMass := by
    have h_assoc : (2 : ENNReal) * X =
        (2000000 : ENNReal) * Kakeya.realRpowENN δ densityFloor * F_enncard * V := by
      dsimp only [X]
      simp [mul_comm, mul_left_comm]
      ; norm_cast
    rw [h_assoc]
    calc
      (2000000 : ENNReal) * Kakeya.realRpowENN δ densityFloor * F_enncard * V
        ≤ Kakeya.realRpowENN δ inputExponent * F_enncard * V := by gcongr
      _ ≤ totalMass := h_input
  have h_two_ne_zero : (2 : ENNReal) ≠ 0 := by norm_num
  have h_two_ne_top : (2 : ENNReal) ≠ ⊤ := by norm_num
  have h3 : X ≤ totalMass / 2 := by
    have h4 : (2 : ENNReal)⁻¹ * ((2 : ENNReal) * X) ≤ (2 : ENNReal)⁻¹ * totalMass := by
      gcongr
    have h5 : (2 : ENNReal)⁻¹ * ((2 : ENNReal) * X) = X := by
      have h51 : (2 : ENNReal)⁻¹ * ((2 : ENNReal) * X) =
          ((2 : ENNReal)⁻¹ * (2 : ENNReal)) * X := by
        rw [mul_assoc]
      rw [h51]
      have h52 : (2 : ENNReal)⁻¹ * (2 : ENNReal) = 1 :=
        ENNReal.inv_mul_cancel h_two_ne_zero h_two_ne_top
      rw [h52, one_mul]
    have h6 : (2 : ENNReal)⁻¹ * totalMass = totalMass / 2 := by
      simp [div_eq_mul_inv, mul_comm]
    rw [h5, h6] at h4
    exact h4
  have h_sum_low : ∑ j ∈ S_low, masses j ≤
      Kakeya.realRpowENN δ densityFloor * (∑ j ∈ S_low, cards j) * V := by
    have h_per : ∀ j ∈ S_low, masses j ≤
        Kakeya.realRpowENN δ densityFloor * cards j * V := by
      intro j hj
      have h_lt : masses j < Kakeya.realRpowENN δ densityFloor * cards j * V :=
        (Finset.mem_filter.mp hj).2
      exact h_lt.le
    let A := Kakeya.realRpowENN δ densityFloor
    have h_sum_eq : ∑ j ∈ S_low, (A * cards j * V) =
        A * (∑ j ∈ S_low, cards j) * V := by
      have h1 : ∑ j ∈ S_low, (A * cards j * V) =
          (∑ j ∈ S_low, (A * cards j)) * V := by
        rw [Finset.sum_mul]
      rw [h1]
      have h2 : (∑ j ∈ S_low, (A * cards j)) = A * (∑ j ∈ S_low, cards j) := by
        rw [Finset.mul_sum]
      rw [h2]
    calc
      ∑ j ∈ S_low, masses j
        ≤ ∑ j ∈ S_low, (A * cards j * V) := Finset.sum_le_sum h_per
      _ = A * (∑ j ∈ S_low, cards j) * V := h_sum_eq
  have h_sum_cards_low : (∑ j ∈ S_low, cards j) ≤ ∑ j : Fin N, cards j := by
    apply Finset.sum_le_sum_of_subset
    exact Finset.filter_subset _ _
  have h_final : Kakeya.realRpowENN δ densityFloor * (∑ j ∈ S_low, cards j) * V ≤ X := by
    dsimp only [X]
    calc
      Kakeya.realRpowENN δ densityFloor * (∑ j ∈ S_low, cards j) * V
        ≤ Kakeya.realRpowENN δ densityFloor * (∑ j : Fin N, cards j) * V := by
          gcongr
      _ ≤ Kakeya.realRpowENN δ densityFloor * (1000000 * F_enncard) * V := by
          gcongr
      _ = (1000000 : ENNReal) * Kakeya.realRpowENN δ densityFloor * F_enncard * V := by
          ring
  exact h_sum_low.trans (h_final.trans h3)

/--
Extract a finite family of indices from a nonempty finset.

Given `S : Finset (Fin N)`, produce `M = S.card`, an injective map
`select : Fin M → Fin N` whose range is exactly `S`, and the sum of
`mass` over the selected indices equals the sum over `S`.
-/
lemma finset_extract_fin {N : ℕ} {S : Finset (Fin N)} (hS : S.Nonempty)
    (mass : Fin N → ENNReal) :
    ∃ (M : ℕ) (hm_pos : 0 < M) (select : Fin M → Fin N),
      Function.Injective select ∧
      Set.range select = (S : Set (Fin N)) ∧
      ∑ k : Fin M, mass (select k) = ∑ i ∈ S, mass i := by
  let M : ℕ := S.card
  have hm_pos : 0 < M := Finset.Nonempty.card_pos hS
  let e : S ≃ Fin M := Finset.equivFin S
  let select : Fin M → Fin N := fun k => (e.symm k : Fin N)
  have h_inj : Function.Injective select := by
    intro k1 k2 h
    have h' : (e.symm k1 : Fin N) = (e.symm k2 : Fin N) := h
    have h'' : e.symm k1 = e.symm k2 := by
      exact Subtype.ext h'
    exact e.symm.injective h''
  have h_range : Set.range select = (S : Set (Fin N)) := by
    ext x
    simp only [Set.mem_range]
    constructor
    · rintro ⟨k, rfl⟩
      exact (e.symm k).property
    · intro hx
      let y : S := ⟨x, hx⟩
      let k : Fin M := e y
      refine ⟨k, ?_⟩
      have h : e.symm k = y := e.symm_apply_apply y
      exact Subtype.ext_iff.mp h
  have h_sum : ∑ k : Fin M, mass (select k) = ∑ i ∈ S, mass i := by
    have h_eq1 : ∑ k : Fin M, mass (select k) =
        ∑ y ∈ S.attach, mass (y : Fin N) := by
      apply Finset.sum_bij (fun (k : Fin M) (_ : k ∈ Finset.univ) => e.symm k)
      · intro k _; exact Finset.mem_attach _ _
      · intro k1 k2 _ _ h; exact e.symm.injective h
      · intro y hy; refine ⟨e y, Finset.mem_univ _, ?_⟩
        simpa using e.symm_apply_apply y
      · intro k _; rfl
    rw [h_eq1]
    rw [Finset.sum_attach]
  exact ⟨M, hm_pos, select, h_inj, h_range, h_sum⟩

/-- If `2 * y ≤ x` in `ENNReal`, then `y ≤ x / 2`. -/
lemma ennreal_half_le {x y : ENNReal} (h : (2 : ENNReal) * y ≤ x) : y ≤ x / 2 := by
  have h_two_ne_zero : (2 : ENNReal) ≠ 0 := by norm_num
  have h_two_ne_top : (2 : ENNReal) ≠ ⊤ := by norm_num
  have h1 : (2 : ENNReal)⁻¹ * ((2 : ENNReal) * y) ≤ (2 : ENNReal)⁻¹ * x := by
    gcongr
  have h2 : (2 : ENNReal)⁻¹ * ((2 : ENNReal) * y) = y := by
    have h3 : (2 : ENNReal)⁻¹ * ((2 : ENNReal) * y) =
        ((2 : ENNReal)⁻¹ * (2 : ENNReal)) * y := by
      rw [← mul_assoc]
    rw [h3]
    have h4 : (2 : ENNReal)⁻¹ * (2 : ENNReal) = 1 :=
      ENNReal.inv_mul_cancel h_two_ne_zero h_two_ne_top
    rw [h4, one_mul]
  have h4 : (2 : ENNReal)⁻¹ * x = x / 2 := by
    simp [div_eq_mul_inv, mul_comm]
  rw [h2, h4] at h1
  exact h1

/-- A positive aggregate density bound implies the total mass is nonzero. -/
lemma mass_pos_from_aggregate {δ : ℝ} {F : Kakeya.TubeFamily δ} {Y : Kakeya.Shading F}
    {e : ℝ} (hδ : 0 < δ) (he : 0 < e) (hF : F.Nonempty)
    (hV_pos : (Kakeya.deltaTubeVolume δ) ≠ 0)
    (h : Kakeya.realRpowENN δ e * F.enncard * Kakeya.deltaTubeVolume δ ≤ Y.mass) :
    Y.mass ≠ 0 := by
  have h1 : 0 < Kakeya.realRpowENN δ e := by
    simp [Kakeya.realRpowENN, Real.rpow_pos_of_pos hδ]
    <;> positivity
  have h21 : 0 < F.card := Finset.Nonempty.card_pos hF
  have h2 : 0 < F.enncard := by
    have h22 : (F.enncard : ENNReal) = ↑(F.card) := by rfl
    rw [h22]
    exact_mod_cast h21
  have h3 : 0 < Kakeya.realRpowENN δ e * F.enncard * Kakeya.deltaTubeVolume δ := by
    positivity
  have h4 : 0 ≤ Y.mass := by positivity
  exact ne_of_gt (h3.trans_le h)

/-- The total shaded mass is bounded by the number of tubes times the tube volume. -/
lemma shading_mass_le_card_mul_volume {δ : ℝ} {F : Kakeya.TubeFamily δ}
    (Y : Kakeya.Shading F) (hδ : 0 < δ) :
    Y.mass ≤ F.enncard * Kakeya.deltaTubeVolume δ := by
  have hvol : ∀ (T : Kakeya.DeltaTube δ), T.volume = Kakeya.deltaTubeVolume δ :=
    tube_volume_scaling.1 δ
  have h1 : ∀ T ∈ F, MeasureTheory.volume (Y.carrier T) ≤ Kakeya.deltaTubeVolume δ := by
    intro T hT
    have h2 : MeasureTheory.volume (Y.carrier T) ≤ MeasureTheory.volume T.carrier :=
      MeasureTheory.measure_mono (Y.subset_tube hT)
    have h3 : MeasureTheory.volume T.carrier = T.volume := by rfl
    rw [h3] at h2
    rw [hvol T] at h2
    exact h2
  calc
    Y.mass
      = ∑ T ∈ F, MeasureTheory.volume (Y.carrier T) := by rfl
    _ ≤ ∑ T ∈ F, Kakeya.deltaTubeVolume δ := Finset.sum_le_sum h1
    _ = F.enncard * Kakeya.deltaTubeVolume δ := by
      have h_sum : ∑ T ∈ F, Kakeya.deltaTubeVolume δ = (F.card : ENNReal) * Kakeya.deltaTubeVolume δ := by
        rw [Finset.sum_const, nsmul_eq_mul]
      rw [h_sum]
      have h_eq : (F.card : ENNReal) = F.enncard := by rfl
      exact congr_arg (fun x => x * Kakeya.deltaTubeVolume δ) h_eq

/-- Convert an `ENNReal` cardinality upper bound by a real power to a real bound. -/
lemma card_le_rpow_real {δ : ℝ} {F : Kakeya.TubeFamily δ} {cardExponent : ℝ}
    (hδ : 0 < δ)
    (h : F.enncard ≤ Kakeya.realRpowENN δ (-cardExponent)) :
    (F.card : ℝ) ≤ Real.rpow δ (-cardExponent) := by
  have h1 : (F.enncard : ENNReal) = ENNReal.ofReal (F.card : ℝ) := by
    have h_eq : (F.enncard : ENNReal) = ↑(F.card) := by rfl
    rw [h_eq]
    have h_cast : (↑(F.card) : ENNReal) = ENNReal.ofReal (↑(F.card) : ℝ) := by
      exact Eq.symm (ENNReal.ofReal_natCast F.card)
    exact h_cast
  rw [h1] at h
  have h2 : 0 ≤ Real.rpow δ (-cardExponent) := Real.rpow_nonneg hδ.le _
  exact (ENNReal.ofReal_le_ofReal_iff h2).mp h

end Kakeya.Assouad

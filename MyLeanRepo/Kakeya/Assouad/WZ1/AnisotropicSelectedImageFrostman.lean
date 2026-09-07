import MyLeanRepo.Kakeya.Assouad.WZ1.ProjectionTheoremFirstLayerStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.ProjectionParameterTuning
import Mathlib.Data.Finset.Card

/-!
# Frostman transfer from coarse cells to the actual selected image

Given `WZ1AnisotropicFrostmanRescalingData`, the actual affine image of the
selected source set inherits a Frostman estimate from the balanced coarse
cells.  This keeps source provenance available for the graph transport.

This lemma does not claim that the actual image is separated at the coarse
scale.  That is a distinct step in the wide branch.
-/

namespace Kakeya.Assouad

open scoped ENNReal
open Finset

/--
The common lower multiplicity of the balanced occupied cells bounds the
selected source cardinality from below.
-/
lemma anisotropic_coarse_card_weighted_le_selected
    {E : DiscreteSet 2}
    {phi : Point2 ≃ᵃ[ℝ] Point2}
    {delta w epsilon_r : ℝ}
    {C : ENNReal}
    (h : WZ1AnisotropicFrostmanRescalingData
      E phi delta w epsilon_r C) :
    (h.fiberMultiplicity : ENNReal) * h.coarse.enncard ≤
      h.selected.enncard := by
  let fiber (q : Point2) : DiscreteSet 2 :=
    h.selected.filter (fun x => h.assignment x = q)
  have hcover :
      h.coarse.biUnion fiber = h.selected := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_biUnion.mp hx with ⟨q, _, hxq⟩
      exact (Finset.mem_filter.mp hxq).1
    · intro hx
      exact Finset.mem_biUnion.mpr
        ⟨h.assignment x, h.assignment_mem x hx,
          Finset.mem_filter.mpr ⟨hx, rfl⟩⟩
  have hdisjoint :
      Set.PairwiseDisjoint (↑h.coarse : Set Point2) fiber := by
    intro first _ second _ hne
    change Disjoint (fiber first) (fiber second)
    rw [Finset.disjoint_left]
    intro x hxFirst hxSecond
    have hfirst :
        h.assignment x = first :=
      (Finset.mem_filter.mp hxFirst).2
    have hsecond :
        h.assignment x = second :=
      (Finset.mem_filter.mp hxSecond).2
    exact hne (hfirst.symm.trans hsecond)
  have hcard :
      h.selected.card =
        ∑ q ∈ h.coarse, (fiber q).card := by
    rw [← hcover, Finset.card_biUnion hdisjoint]
  calc
    (h.fiberMultiplicity : ENNReal) * h.coarse.enncard =
        ∑ _q ∈ h.coarse,
          (h.fiberMultiplicity : ENNReal) := by
      simp [DiscreteSet.enncard, mul_comm]
    _ ≤ ∑ q ∈ h.coarse, ((fiber q).card : ENNReal) := by
      apply Finset.sum_le_sum
      intro q hq
      exact_mod_cast (h.fiber_comparable q hq).1
    _ = (h.selected.card : ENNReal) := by
      exact_mod_cast hcard.symm
    _ = h.selected.enncard := by
      rfl

/--
The selected set, pushed forward through the normalization affine map,
inherits a Frostman bound from the coarse grid.

The constant loss is `4`: every selected image lies within `rho` of its
coarse cell, every cell has at most `2 * m` selected sources, and a radius
`r ≥ rho` expands to at most `2 * r`.
-/
lemma anisotropic_selected_image_frostman
    {E : DiscreteSet 2}
    {phi : Point2 ≃ᵃ[ℝ] Point2}
    {delta w epsilon_r : ℝ}
    {C : ENNReal}
    (h : WZ1AnisotropicFrostmanRescalingData E phi delta w epsilon_r C)
    (hdelta_pos : 0 < delta)
    (hw_pos : 0 < w)
    (hC_one : 1 ≤ C)
    (hdelta_w : delta ≤ w)
    (hepsilon_r_pos : 0 < epsilon_r) :
    DiscreteSet.IsFrostman (h.selected.image phi) (delta / w) 1
      (4 * (Kakeya.realRpowENN (w / delta) epsilon_r * C)) := by
  set rho : ℝ := delta / w with hrho_def
  set S : DiscreteSet 2 := h.selected.image phi with hS_def
  set Q : DiscreteSet 2 := h.coarse with hQ_def
  set m : ℕ := h.fiberMultiplicity with hm_def
  set C_coarse : ENNReal :=
    Kakeya.realRpowENN (w / delta) epsilon_r * C with hC_coarse_def

  have hrho_pos : 0 < delta / w := by positivity

  have hphi_inj : Function.Injective phi := phi.injective
  have hS_card : S.enncard = h.selected.enncard := by
    simp [hS_def, DiscreteSet.enncard,
      Finset.card_image_of_injective _ hphi_inj]

  have hm_pos : 0 < m := h.fiberMultiplicity_pos

  let fiber (q : Point2) : DiscreteSet 2 :=
    h.selected.filter (fun x => h.assignment x = q)

  have h_fiber_cover :
      ∀ x ∈ h.selected, x ∈ fiber (h.assignment x) := by
    intro x hx
    simp [fiber, hx]

  have h_fiber_disj :
      ∀ q q' : Point2, q ≠ q' →
        Disjoint (fiber q) (fiber q') := by
    intro q q' hne
    rw [Finset.disjoint_left]
    intro a ha
    have hq : h.assignment a = q :=
      (Finset.mem_filter.mp ha).2
    intro ha'
    have hq' : h.assignment a = q' :=
      (Finset.mem_filter.mp ha').2
    rw [hq] at hq'
    exact hne hq'

  have h_disj' :
      Set.PairwiseDisjoint (↑Q : Set Point2) fiber := by
    intro q _ q' _ hne
    exact h_fiber_disj q q' hne

  have hQ_le_S : (m : ENNReal) * Q.enncard ≤ S.enncard := by
    have h_union : Q.biUnion fiber = h.selected := by
      apply Finset.ext
      intro x
      constructor
      · intro hx
        rcases Finset.mem_biUnion.mp hx with ⟨q, _, hx'⟩
        exact (Finset.mem_filter.mp hx').1
      · intro hx
        apply Finset.mem_biUnion.mpr
        exact
          ⟨h.assignment x, h.assignment_mem x hx,
            h_fiber_cover x hx⟩
    have h_sum :
        (Q.biUnion fiber).card =
          ∑ q ∈ Q, (fiber q).card :=
      Finset.card_biUnion h_disj'
    have h_sum2 :
        ∑ q ∈ Q, (fiber q).card = h.selected.card := by
      rw [← h_sum, h_union]
    calc
      (m : ENNReal) * Q.enncard
          = ∑ q ∈ Q, (m : ENNReal) := by
            simp [DiscreteSet.enncard, mul_comm]
      _ ≤ ∑ q ∈ Q, ((fiber q).card : ENNReal) := by
        apply Finset.sum_le_sum
        intro q hq
        exact_mod_cast (h.fiber_comparable q hq).1
      _ = (h.selected.card : ENNReal) := by
        exact_mod_cast h_sum2
      _ = S.enncard := by
        exact_mod_cast hS_card.symm

  have hC_coarse_one : (1 : ENNReal) ≤ C_coarse := by
    have h1 : 1 ≤ w / delta :=
      (one_le_div hdelta_pos).mpr hdelta_w
    have h3 :
        (1 : ENNReal) ≤
          Kakeya.realRpowENN (w / delta) epsilon_r := by
      simpa [Kakeya.realRpowENN, ENNReal.ofReal_le_ofReal] using
        Real.one_le_rpow h1 hepsilon_r_pos.le
    dsimp only [C_coarse]
    have h4 :
        (1 : ENNReal) * (1 : ENNReal) ≤
          Kakeya.realRpowENN (w / delta) epsilon_r * C :=
      mul_le_mul' h3 hC_one
    simpa using h4

  intro x r hrho_hr hr_one

  let B_S : DiscreteSet 2 :=
    S.filter (fun y => dist y x ≤ r)
  let g : Point2 → Point2 :=
    fun y => h.assignment (phi.symm y)

  have h1 :
      ∀ y ∈ B_S, g y ∈ Q ∧ dist (g y) x ≤ r + rho := by
    intro y hy
    have h_yS : y ∈ S := (Finset.mem_filter.mp hy).1
    have h_yr : dist y x ≤ r := (Finset.mem_filter.mp hy).2
    rcases Finset.mem_image.mp h_yS with ⟨z, hz, rfl⟩
    have h_close :
        dist (phi z) (h.assignment z) ≤ rho :=
      h.assignment_close z hz
    have h_mem : h.assignment z ∈ Q :=
      h.assignment_mem z hz
    have h_g_eq :
        g (phi z) = h.assignment z := by
      simp [g]
    have h_dist :
        dist (h.assignment z) x ≤ r + rho := by
      have h_tri :
          dist (h.assignment z) x ≤
            dist (h.assignment z) (phi z) + dist (phi z) x :=
        dist_triangle _ _ _
      have h_comm :
          dist (h.assignment z) (phi z) =
            dist (phi z) (h.assignment z) :=
        dist_comm _ _
      rw [h_comm] at h_tri
      linarith
    exact
      ⟨by rw [h_g_eq]; exact h_mem,
        by rw [h_g_eq]; exact h_dist⟩

  let image_g : DiscreteSet 2 := B_S.image g
  have h_image_sub :
      image_g ⊆
        Q.filter (fun q => dist q x ≤ r + rho) := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨y, hy, rfl⟩
    exact Finset.mem_filter.mpr (h1 y hy)

  have h_fiber_bound :
      ∀ q ∈ image_g,
        (B_S.filter (fun y => g y = q)).card ≤ 2 * m := by
    intro q hq
    let f : Point2 → Point2 := fun y => phi.symm y
    have h_inj : Function.Injective f := phi.symm.injective
    have h_image_sub :
        (B_S.filter (fun y => g y = q)).image f ⊆
          fiber q := by
      intro w hw
      rcases Finset.mem_image.mp hw with ⟨y, hy, rfl⟩
      have h_yB : y ∈ B_S :=
        (Finset.mem_filter.mp hy).1
      have h_yS : y ∈ S :=
        (Finset.mem_filter.mp h_yB).1
      have h_gyq : g y = q :=
        (Finset.mem_filter.mp hy).2
      rcases Finset.mem_image.mp h_yS with
        ⟨z', hz', hy_eq⟩
      have h_asgn : h.assignment z' = q := by
        have h_gyq' :
            h.assignment (phi.symm y) = q := by
          simpa [g] using h_gyq
        have h_symm : phi.symm y = z' := by
          rw [← hy_eq]
          simp
        rwa [h_symm] at h_gyq'
      have h_fy : f y = z' := by
        simp [f, ← hy_eq]
      rw [h_fy]
      exact Finset.mem_filter.mpr ⟨hz', h_asgn⟩
    have h_card1 :
        ((B_S.filter (fun y => g y = q)).image f).card =
          (B_S.filter (fun y => g y = q)).card :=
      Finset.card_image_of_injective _ h_inj
    have h_card2 :
        ((B_S.filter (fun y => g y = q)).image f).card ≤
          (fiber q).card :=
      Finset.card_le_card h_image_sub
    have hq' : q ∈ Q := by
      rcases Finset.mem_image.mp hq with ⟨a, ha, rfl⟩
      exact (h1 a ha).1
    rw [← h_card1]
    exact h_card2.trans (h.fiber_comparable q hq').2

  have h_partition :
      B_S =
        image_g.biUnion
          (fun q => B_S.filter (fun y => g y = q)) := by
    ext y
    simp only [Finset.mem_biUnion]
    constructor
    · intro hy
      exact
        ⟨g y, Finset.mem_image.mpr ⟨y, hy, rfl⟩,
          Finset.mem_filter.mpr ⟨hy, rfl⟩⟩
    · rintro ⟨q, _, hy⟩
      exact (Finset.mem_filter.mp hy).1

  have h_disj2 :
      Set.PairwiseDisjoint (↑image_g : Set Point2)
        (fun q => B_S.filter (fun y => g y = q)) := by
    intro q _ q' _ hne
    change
      Disjoint
        (B_S.filter (fun y => g y = q))
        (B_S.filter (fun y => g y = q'))
    rw [Finset.disjoint_left]
    intro y hy hy'
    have hq : g y = q :=
      (Finset.mem_filter.mp hy).2
    have hq' : g y = q' :=
      (Finset.mem_filter.mp hy').2
    exact hne (hq.symm.trans hq')

  have h_card_le :
      (B_S.card : ENNReal) ≤
        (2 * m : ENNReal) *
          (Q.filter (fun q => dist q x ≤ r + rho)).card := by
    have h_sum_card :
        ((image_g.biUnion
            (fun q => B_S.filter (fun y => g y = q))).card :
            ENNReal) =
          ∑ q ∈ image_g,
            ((B_S.filter (fun y => g y = q)).card : ENNReal) := by
      exact_mod_cast Finset.card_biUnion h_disj2
    have h_sum :
        ∑ q ∈ image_g,
            ((B_S.filter (fun y => g y = q)).card : ENNReal) ≤
          ∑ _q ∈ image_g, (2 * m : ENNReal) := by
      apply Finset.sum_le_sum
      intro q hq
      exact_mod_cast h_fiber_bound q hq
    calc
      (B_S.card : ENNReal) =
          ((image_g.biUnion
              (fun q => B_S.filter (fun y => g y = q))).card :
              ENNReal) := by
            exact_mod_cast congrArg Finset.card h_partition
      _ = ∑ q ∈ image_g,
            ((B_S.filter (fun y => g y = q)).card : ENNReal) :=
        h_sum_card
      _ ≤ ∑ _q ∈ image_g, (2 * m : ENNReal) := h_sum
      _ = (2 * m : ENNReal) * (image_g.card : ENNReal) := by
        simp [mul_comm]
      _ ≤
          (2 * m : ENNReal) *
            ((Q.filter (fun q => dist q x ≤ r + rho)).card :
              ENNReal) := by
        gcongr

  by_cases hcase : r + rho ≤ 1
  · have hrho_le_rho : rho ≤ r + rho := by linarith
    have h_frost :
        Q.ballCount x (r + rho) ≤
          C_coarse * Kakeya.realRpowENN (r + rho) 1 *
            Q.enncard :=
      h.coarse_frostman x (r + rho) hrho_le_rho hcase
    have h_rpow :
        Kakeya.realRpowENN (r + rho) 1 =
          ENNReal.ofReal (r + rho) := by
      simp [Kakeya.realRpowENN]
    have h_rpow_r :
        Kakeya.realRpowENN r 1 = ENNReal.ofReal r := by
      simp [Kakeya.realRpowENN]
    have h_r_le :
        ENNReal.ofReal (r + rho) ≤
          2 * ENNReal.ofReal r := by
      have hreal : r + rho ≤ 2 * r := by
        linarith [hrho_hr]
      calc
        ENNReal.ofReal (r + rho) ≤
            ENNReal.ofReal (2 * r) :=
          ENNReal.ofReal_mono hreal
        _ = 2 * ENNReal.ofReal r := by
          rw [ENNReal.ofReal_mul (by norm_num)]
          norm_num
    calc
      (B_S.card : ENNReal) ≤
          (2 * m : ENNReal) * Q.ballCount x (r + rho) :=
        h_card_le
      _ ≤
          (2 * m : ENNReal) *
            (C_coarse * ENNReal.ofReal (r + rho) *
              Q.enncard) := by
        rw [h_rpow] at h_frost
        gcongr
      _ =
          2 * C_coarse * ENNReal.ofReal (r + rho) *
            ((m : ENNReal) * Q.enncard) := by
        ring
      _ ≤
          2 * C_coarse * ENNReal.ofReal (r + rho) *
            S.enncard := by
        gcongr
      _ ≤
          2 * C_coarse * (2 * ENNReal.ofReal r) *
            S.enncard := by
        gcongr
      _ =
          4 * C_coarse * Kakeya.realRpowENN r 1 *
            S.enncard := by
        rw [h_rpow_r]
        ring
  · have h_r_gt_half : 1 / 2 < r := by
      by_contra h2
      have h3 : r ≤ 1 / 2 := by linarith
      linarith [hrho_hr]
    have h5 :
        (1 : ENNReal) ≤
          4 * C_coarse * ENNReal.ofReal r := by
      have h6 :
          ENNReal.ofReal (1 / 2 : ℝ) ≤
            ENNReal.ofReal r :=
        ENNReal.ofReal_le_ofReal h_r_gt_half.le
      have h_base :
          (1 : ENNReal) ≤
            (4 : ENNReal) * (1 : ENNReal) *
              ENNReal.ofReal (1 / 2 : ℝ) := by
        have h1 :
            (4 : ENNReal) * (1 : ENNReal) =
              (4 : ENNReal) := by simp
        have h2 :
            (4 : ENNReal) * ENNReal.ofReal (1 / 2 : ℝ) =
              ENNReal.ofReal (2 : ℝ) := by
          have h3 :
              (4 : ENNReal) =
                ENNReal.ofReal (4 : ℝ) := by simp
          rw [h3]
          have h4 :
              ENNReal.ofReal (4 : ℝ) *
                  ENNReal.ofReal (1 / 2 : ℝ) =
                ENNReal.ofReal
                  ((4 : ℝ) * (1 / 2 : ℝ)) := by
            rw [← ENNReal.ofReal_mul (by norm_num)]
          rw [h4]
          norm_num
        rw [h1, h2]
        simp
      calc
        (1 : ENNReal) ≤
            4 * 1 * ENNReal.ofReal (1 / 2 : ℝ) :=
          h_base
        _ ≤ 4 * C_coarse * ENNReal.ofReal r := by
          gcongr
    have h_triv : (B_S.card : ENNReal) ≤ S.enncard := by
      have hnat : B_S.card ≤ S.card := by
        apply Finset.card_le_card
        dsimp only [B_S]
        exact Finset.filter_subset _ _
      simpa [DiscreteSet.enncard] using
        (show (B_S.card : ENNReal) ≤ (S.card : ENNReal) by
          exact_mod_cast hnat)
    have h_rpow_r :
        Kakeya.realRpowENN r 1 = ENNReal.ofReal r := by
      simp [Kakeya.realRpowENN]
    have h9 :
        S.enncard ≤
          4 * C_coarse * ENNReal.ofReal r * S.enncard := by
      simpa [one_mul] using
        (mul_le_mul_left h5 S.enncard)
    calc
      (B_S.card : ENNReal) ≤ S.enncard := h_triv
      _ ≤
          4 * C_coarse * ENNReal.ofReal r * S.enncard :=
        h9
      _ =
          4 * C_coarse * Kakeya.realRpowENN r 1 *
            S.enncard := by
        rw [h_rpow_r]

/-- Derive the same Frostman estimate with any larger constant. -/
lemma anisotropic_selected_image_frostman_of_le
    {E : DiscreteSet 2}
    {phi : Point2 ≃ᵃ[ℝ] Point2}
    {delta w epsilon_r : ℝ}
    {C C' : ENNReal}
    (h : WZ1AnisotropicFrostmanRescalingData E phi delta w epsilon_r C)
    (hdelta_pos : 0 < delta)
    (hw_pos : 0 < w)
    (hC_one : 1 ≤ C)
    (hdelta_w : delta ≤ w)
    (hepsilon_r_pos : 0 < epsilon_r)
    (hC' :
      4 * (Kakeya.realRpowENN (w / delta) epsilon_r * C) ≤ C') :
    DiscreteSet.IsFrostman
      (h.selected.image phi) (delta / w) 1 C' :=
  (anisotropic_selected_image_frostman
    h hdelta_pos hw_pos hC_one hdelta_w hepsilon_r_pos).mono hC'

end Kakeya.Assouad

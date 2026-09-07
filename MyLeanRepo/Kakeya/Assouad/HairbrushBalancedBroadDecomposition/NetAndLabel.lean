import MyLeanRepo.Kakeya.Assouad.HairbrushBalancedBroadDecomposition.AngularStoppingHelpers
import MyLeanRepo.Kakeya.Assouad.HairbrushBalancedBroadDecomposition.MeasurableLabel
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

/-!
# Direction net and measurable labeling

Given pattern centers and pairwise disjoint measurable through-pattern sets,
construct a finite direction net, measurable label function, unit centers,
confinement property, and label overlap bound.
-/

noncomputable section

open Metric Finset InnerProductGeometry Real MeasureTheory Set

attribute [local instance] Classical.propDecidable

namespace Kakeya.Assouad

/-- Construct a direction net and measurable labeling from pattern centers. -/
lemma net_and_label
    (centers : Finset Point3)
    (hcenters : ∀ v ∈ centers, ‖v‖ = 1)
    (theta : ℝ)
    (htheta : 0 < theta)
    (htheta1 : theta ≤ 1 / 2)
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    (patToCenter : ι → Point3)
    (hpat : ∀ i, patToCenter i ∈ centers)
    (A : ι → Set Point3)
    (hA : ∀ i, MeasurableSet (A i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (A i) (A j)) :
    ∃ (labelCount : ℕ) (hlabelCount_pos : 0 < labelCount)
      (label : Point3 → Fin labelCount)
      (center : Fin labelCount → Point3),
      Measurable label ∧
      (∀ j, ‖center j‖ = 1) ∧
      (∀ i x, x ∈ A i → ∀ v, ‖v‖ = 1 →
        hairbrushAcuteDirectionAngle v (patToCenter i) ≤ theta →
        hairbrushAcuteDirectionAngle v (center (label x)) ≤ 2 * theta) ∧
      (∀ (v0 : Point3), ‖v0‖ = 1 →
        (Finset.univ.filter (fun j : Fin labelCount =>
          hairbrushAcuteDirectionAngle (center j) v0 ≤ 2 * theta)).card ≤ 1000) := by
  -- Construct a canonical unit vector for fallback
  let eUnit : Point3 := EuclideanSpace.single 0 1
  have heUnit_norm : ‖eUnit‖ = 1 := by
    have h_sq : ‖eUnit‖ ^ 2 = 1 := by
      have h41 : ‖eUnit‖ ^ 2 = inner ℝ eUnit eUnit := (real_inner_self_eq_norm_sq eUnit).symm
      rw [h41]
      have h42 : inner ℝ eUnit eUnit = 1 := by
        rw [EuclideanSpace.inner_single_left 0 (1 : ℝ) eUnit]
        simp [eUnit]
      exact h42
    have h_nonneg : 0 ≤ ‖eUnit‖ := by positivity
    nlinarith

  -- Step 1: Maximal theta-separated subset of centers
  rcases maximal_acute_separated_subset htheta hcenters with ⟨N, hN_sub, hN_sep, hN_cover⟩

  -- Ensure nonempty net
  let N' : Finset Point3 := if N.Nonempty then N else {eUnit}

  have hN'_eq_nonempty : N.Nonempty → N' = N := by
    intro h; simp [N', h]
  have hN'_eq_empty : ¬N.Nonempty → N' = {eUnit} := by
    intro h; simp [N', h]

  have hN'_nonempty : N'.Nonempty := by
    by_cases h : N.Nonempty
    · rw [hN'_eq_nonempty h]; exact h
    · rw [hN'_eq_empty h]; exact Finset.singleton_nonempty eUnit

  have hN'_sep : ∀ v ∈ N', ∀ w ∈ N', v ≠ w → theta ≤ hairbrushAcuteDirectionAngle v w := by
    by_cases h : N.Nonempty
    · rw [hN'_eq_nonempty h]; exact hN_sep
    · rw [hN'_eq_empty h]
      intro v hv w hw hne
      simp only [Finset.mem_singleton] at hv hw
      rw [hv, hw] at hne <;> tauto

  have hN'_unit : ∀ v ∈ N', ‖v‖ = 1 := by
    by_cases h : N.Nonempty
    · rw [hN'_eq_nonempty h]
      intro v hv
      exact hcenters v (hN_sub hv)
    · rw [hN'_eq_empty h]
      intro v hv
      have h5 : v = eUnit := Finset.mem_singleton.mp hv
      rw [h5]; exact heUnit_norm

  have h_centers_empty_of_N_empty : ¬N.Nonempty → centers = ∅ := by
    intro h
    by_contra h2
    have h3 : centers.Nonempty := Finset.nonempty_iff_ne_empty.mpr h2
    rcases h3 with ⟨v, hv⟩
    rcases hN_cover v hv with ⟨n, hn, _⟩
    have h4 : N.Nonempty := ⟨n, hn⟩
    exact h h4

  have hN'_cover : ∀ v ∈ centers, ∃ n ∈ N', hairbrushAcuteDirectionAngle v n < theta := by
    by_cases h : N.Nonempty
    · rw [hN'_eq_nonempty h]
      intro v hv
      rcases hN_cover v hv with ⟨n, hn, hangle⟩
      exact ⟨n, hn, hangle⟩
    · have hce : centers = ∅ := h_centers_empty_of_N_empty h
      intro v hv
      rw [hce] at hv
      simp at hv

  let labelCount := N'.card
  have hlabelCount_pos : 0 < labelCount := Finset.card_pos.mpr hN'_nonempty

  -- Enumerate net points by Fin labelCount
  have h_card : Fintype.card {x // x ∈ N'} = labelCount := by
    simp [labelCount]
  let e0 : {x // x ∈ N'} ≃ Fin (Fintype.card {x // x ∈ N'}) := Fintype.equivFin {x // x ∈ N'}
  let e : {x // x ∈ N'} ≃ Fin labelCount :=
    e0.trans (Equiv.cast (congr_arg Fin h_card))
  let center : Fin labelCount → Point3 := fun j => (e.symm j).val

  have hcenter_in_N' : ∀ j, center j ∈ N' := fun j => (e.symm j).property
  have hcenter_unit : ∀ j, ‖center j‖ = 1 := fun j => hN'_unit (center j) (hcenter_in_N' j)
  have hcenter_inj : Function.Injective center := by
    intro j k h
    have h1 : (e.symm j).val = (e.symm k).val := h
    have h2 : e.symm j = e.symm k := by exact Subtype.ext h1
    have h3 : j = k := by exact Equiv.injective (e.symm) h2
    exact h3

  -- Step 2: Assign a nearby net point to each pattern
  let h_exists (i : ι) : ∃ n, n ∈ N' ∧ hairbrushAcuteDirectionAngle (patToCenter i) n < theta := by
    rcases hN'_cover (patToCenter i) (hpat i) with ⟨n, hn, hangle⟩
    exact ⟨n, hn, hangle⟩
  let n_i (i : ι) : Point3 := Classical.choose (h_exists i)
  have hn_i_in : ∀ i, n_i i ∈ N' := fun i => (Classical.choose_spec (h_exists i)).1
  have hn_i_angle : ∀ i, hairbrushAcuteDirectionAngle (patToCenter i) (n_i i) < theta :=
    fun i => (Classical.choose_spec (h_exists i)).2

  let lab : ι → Fin labelCount := fun i => e ⟨n_i i, hn_i_in i⟩
  have hcenter_lab : ∀ i, center (lab i) = n_i i := by
    intro i
    simp [center, lab]

  let default : Fin labelCount := ⟨0, hlabelCount_pos⟩
  let label : Point3 → Fin labelCount := measurableLabel A lab default

  have hlabel_measurable : Measurable label :=
    measurableLabel_measurable A hA lab default

  -- Step 3: Confinement
  have hconfinement : ∀ i x, x ∈ A i → ∀ v, ‖v‖ = 1 →
      hairbrushAcuteDirectionAngle v (patToCenter i) ≤ theta →
      hairbrushAcuteDirectionAngle v (center (label x)) ≤ 2 * theta := by
    intro i x hx v hv hvt
    have hlabel_eq : label x = lab i :=
      measurableLabel_at_disjoint A lab default hdisj hx
    rw [hlabel_eq]
    have h_triangle : hairbrushAcuteDirectionAngle v (center (lab i)) ≤
        hairbrushAcuteDirectionAngle v (patToCenter i) +
        hairbrushAcuteDirectionAngle (patToCenter i) (center (lab i)) :=
      acute_direction_angle_triangle hv (hcenters (patToCenter i) (hpat i)) (hcenter_unit (lab i))
    have h_angle2 : hairbrushAcuteDirectionAngle (patToCenter i) (center (lab i)) < theta := by
      rw [hcenter_lab i]
      exact hn_i_angle i
    linarith

  -- Step 4: Label overlap bound
  have hoverlap : ∀ (v0 : Point3), ‖v0‖ = 1 →
      (Finset.univ.filter (fun j : Fin labelCount =>
        hairbrushAcuteDirectionAngle (center j) v0 ≤ 2 * theta)).card ≤ 1000 := by
    intro v0 hv0
    let J : Finset (Fin labelCount) := Finset.univ.filter (fun j =>
      hairbrushAcuteDirectionAngle (center j) v0 ≤ 2 * theta)
    let S : Finset Point3 := Finset.image center J
    have hS_sub : S ⊆ N' := by
      intro v hv
      rcases Finset.mem_image.mp hv with ⟨j, _, rfl⟩
      exact hcenter_in_N' j
    have hS_unit : ∀ v ∈ S, ‖v‖ = 1 := fun v hv => hN'_unit v (hS_sub hv)
    have hS_sep : ∀ v ∈ S, ∀ w ∈ S, v ≠ w → theta ≤ hairbrushAcuteDirectionAngle v w := by
      intro v hv w hw hne
      exact hN'_sep v (hS_sub hv) w (hS_sub hw) hne
    have hS_cap : ∀ v ∈ S, hairbrushAcuteDirectionAngle v v0 ≤ 2 * theta := by
      intro v hv
      rcases Finset.mem_image.mp hv with ⟨j, hj, rfl⟩
      have h5 : j ∈ J := hj
      have h6 : hairbrushAcuteDirectionAngle (center j) v0 ≤ 2 * theta := by
        simpa [J, Finset.mem_filter] using h5
      exact h6
    have hS_card : S.card ≤ 1000 :=
      constant_direction_packing_half htheta htheta1 hS_unit hS_sep v0 hv0 hS_cap
    have h_card_eq : S.card = J.card := by
      rw [Finset.card_image_of_injective _ hcenter_inj]
    rw [h_card_eq] at hS_card
    exact hS_card

  exact ⟨labelCount, hlabelCount_pos, label, center, hlabel_measurable, hcenter_unit, hconfinement, hoverlap⟩

end Kakeya.Assouad

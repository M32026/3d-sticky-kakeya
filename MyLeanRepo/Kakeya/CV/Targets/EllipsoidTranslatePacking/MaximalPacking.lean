import MyLeanRepo.Kakeya.CV.Targets.EllipsoidTranslatePacking.Basic
import MyLeanRepo.Kakeya.CV.Targets.EllipsoidTranslatePacking.VolumeScaling
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Order.SuccPred.Archimedean

/-!
# Maximal finite packing by ellipsoid translates

Given a linear automorphism `A` and scale `η > 0` such that the doubled
ellipsoid `scaledEllipsoid A (2*η) 0` lies in the unit ball, there exists a
finite set of centers `S` with `‖z‖ ≤ 1/2` for all `z ∈ S`, such that the
ellipsoids `scaledEllipsoid A η z` are pairwise disjoint and `S` has maximum
possible cardinality among all such packings.

Also provides `exists_maximal_packing_max`, which additionally guarantees that
the packing is maximal by inclusion (no further disjoint center can be added).
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Kakeya.CV

/-- A scaled ellipsoid centered at 0 is just the linear image of the ball. -/
lemma scaledEllipsoid_zero (A : Point 3 ≃ₗ[ℝ] Point 3) (η : ℝ) :
    scaledEllipsoid A η 0 = A '' Metric.closedBall (0 : Point 3) η := by
  ext x
  simp only [scaledEllipsoid, Set.mem_vadd_set]
  constructor
  · rintro ⟨y, hy, h_eq⟩
    have h : y = x := by simpa [zero_add] using h_eq
    simpa [h] using hy
  · intro hx
    refine ⟨x, hx, ?_⟩
    simp [zero_add]

/-- A scaled ellipsoid is a measurable set. -/
lemma measurableSet_scaledEllipsoid
    (A : Point 3 ≃ₗ[ℝ] Point 3) (η : ℝ) (z : Point 3) :
    MeasurableSet (scaledEllipsoid A η z) := by
  let A' := A.toContinuousLinearEquiv
  have h1 : IsCompact (Metric.closedBall (0 : Point 3) η) := isCompact_closedBall _ _
  have h2 : IsCompact (A '' Metric.closedBall (0 : Point 3) η) :=
    h1.image A'.continuous
  have h3 : IsCompact (scaledEllipsoid A η z) := by
    have h4 : scaledEllipsoid A η z =
        (fun x : Point 3 => z + x) '' (A '' Metric.closedBall (0 : Point 3) η) := by
      ext y
      simp [scaledEllipsoid, Set.mem_vadd_set, Set.mem_image]
      <;> aesop
    rw [h4]
    exact h2.image (continuous_const_add z)
  exact h3.isClosed.measurableSet

/-- The volume of a scaled ellipsoid is independent of its translation center. -/
lemma volume_scaledEllipsoid_translate
    (A : Point 3 ≃ₗ[ℝ] Point 3) (η : ℝ) (z : Point 3) :
    volume (scaledEllipsoid A η z) = volume (scaledEllipsoid A η 0) := by
  let t : Point 3 → Point 3 := fun x => z + x
  let t_inv : Point 3 → Point 3 := fun x => -z + x
  let s : Set (Point 3) := scaledEllipsoid A η 0
  let s0 : Set (Point 3) := A '' Metric.closedBall (0 : Point 3) η
  have hs : s = s0 := scaledEllipsoid_zero A η
  have h_eq1 : scaledEllipsoid A η z = t '' s := by
    rw [hs]
    unfold scaledEllipsoid t s0
    <;> rfl
  have h_eq2 : t '' s = t_inv ⁻¹' s := by
    ext y
    simp only [Set.mem_image, Set.mem_preimage, t, t_inv]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have h : -z + (z + x) = x := by abel
      rw [h]
      exact hx
    · intro hy
      refine ⟨-z + y, hy, ?_⟩
      abel
  rw [h_eq1, h_eq2]
  have hmp : MeasurePreserving t_inv := measurePreserving_add_left volume (-z)
  exact hmp.measure_preimage (measurableSet_scaledEllipsoid A η 0).nullMeasurableSet

/-- A finite set `S` is a valid packing if all centers are within `1/2` of the
origin and the corresponding scaled ellipsoids are pairwise disjoint. -/
def IsPacking (A : Point 3 ≃ₗ[ℝ] Point 3) (η : ℝ)
    (S : Finset (Point 3)) : Prop :=
  (∀ z ∈ S, ‖z‖ ≤ 1 / 2) ∧
  (↑S : Set (Point 3)).PairwiseDisjoint (fun z => scaledEllipsoid A η z)

/-- Existence of a maximum-cardinality finite packing. -/
theorem exists_maximal_packing
    (A : Point 3 ≃ₗ[ℝ] Point 3) (η : ℝ) (hη : 0 < η)
    (h : scaledEllipsoid A (2 * η) 0 ⊆ unitBall 3) :
    ∃ (S : Finset (Point 3)), IsPacking A η S ∧
      ∀ (T : Finset (Point 3)), IsPacking A η T → T.card ≤ S.card := by
  let V : ENNReal := volume (scaledEllipsoid A η 0)
  let U : ENNReal := volume (unitBall 3)
  have hV_pos : 0 < V := volume_scaledEllipsoid_pos A η hη 0
  have hU_lt_top : U < ⊤ := volume_unitBall_lt_top
  have hV_lt_top : V < ⊤ := by
    have h_sub : scaledEllipsoid A η 0 ⊆ unitBall 3 :=
      center_containment A η hη 0 h (by norm_num)
    have h_le : V ≤ U := measure_mono h_sub
    exact lt_of_le_of_lt h_le hU_lt_top
  let X : ENNReal := U / V
  have hX_lt_top : X < ⊤ := ENNReal.div_lt_top hU_lt_top.ne hV_pos.ne'
  have h_card_bound : ∀ (S : Finset (Point 3)), IsPacking A η S →
      S.card ≤ Nat.ceil X.toReal := by
    intro S hS
    have h1 : ∀ z ∈ S, scaledEllipsoid A η z ⊆ unitBall 3 := by
      intro z hz
      exact center_containment A η hη z h (hS.1 z hz)
    have h_disj : (↑S : Set (Point 3)).PairwiseDisjoint (fun z => scaledEllipsoid A η z) :=
      hS.2
    have h_meas : ∀ z ∈ S, MeasurableSet (scaledEllipsoid A η z) :=
      fun z _ => measurableSet_scaledEllipsoid A η z
    have h_union_sub : (⋃ z ∈ S, scaledEllipsoid A η z) ⊆ unitBall 3 := by
      intro x hx
      simp only [Set.mem_iUnion₂] at hx
      rcases hx with ⟨w, hwS, hxw⟩
      exact h1 w hwS hxw
    have h_sum : volume (⋃ z ∈ S, scaledEllipsoid A η z) =
        ∑ z ∈ S, volume (scaledEllipsoid A η z) :=
      MeasureTheory.measure_biUnion_finset h_disj h_meas
    have h_vol : ∑ z ∈ S, volume (scaledEllipsoid A η z) ≤ U := by
      rw [←h_sum]
      exact measure_mono h_union_sub
    have h_all_same : ∑ z ∈ S, volume (scaledEllipsoid A η z) =
        (S.card : ENNReal) * V := by
      have h_eq : ∀ z ∈ S, volume (scaledEllipsoid A η z) = V := by
        intro z _
        exact volume_scaledEllipsoid_translate A η z
      rw [Finset.sum_congr rfl h_eq]
      simp [Finset.sum_const]
    rw [h_all_same] at h_vol
    have h9 : (S.card : ENNReal) * V ≤ U := h_vol
    have h10 : (S.card : ENNReal) ≤ U / V := by
      calc
        (S.card : ENNReal)
          = (S.card : ENNReal) * V * V⁻¹ := by
            rw [mul_assoc, ENNReal.mul_inv_cancel hV_pos.ne' hV_lt_top.ne, mul_one]
        _ ≤ U * V⁻¹ := by gcongr
        _ = U / V := by rfl
    have h11 : (S.card : ENNReal) ≤ X := h10
    have h_iff : ENNReal.toReal (S.card : ENNReal) ≤ X.toReal ↔ (S.card : ENNReal) ≤ X :=
      ENNReal.toReal_le_toReal (by simp) hX_lt_top.ne
    have h13 : ENNReal.toReal (S.card : ENNReal) ≤ X.toReal := h_iff.mpr h11
    have h12 : (S.card : ℝ) ≤ X.toReal := by simpa using h13
    have h14 : (S.card : ℝ) ≤ (Nat.ceil X.toReal : ℝ) := by
      calc
        (S.card : ℝ) ≤ X.toReal := h12
        _ ≤ (Nat.ceil X.toReal : ℝ) := Nat.le_ceil X.toReal
    exact_mod_cast h14
  let cards : Set ℕ := {k | ∃ (S : Finset (Point 3)), IsPacking A η S ∧ S.card = k}
  have h_cards_nonempty : cards.Nonempty := by
    refine ⟨0, ?_⟩
    refine ⟨(∅ : Finset (Point 3)), ?_ , rfl⟩
    exact ⟨by simp, by simp [Set.PairwiseDisjoint]⟩
  have h_cards_bdd : BddAbove cards := by
    use Nat.ceil X.toReal
    intro k hk
    rcases hk with ⟨S, hS, rfl⟩
    exact h_card_bound S hS
  have h_main : ∃ (k : ℕ), IsGreatest cards k :=
    BddAbove.exists_isGreatest_of_nonempty h_cards_bdd h_cards_nonempty
  rcases h_main with ⟨k, hk⟩
  have hk_in : k ∈ cards := hk.1
  have hk_max : ∀ (x : ℕ), x ∈ cards → x ≤ k := hk.2
  rcases hk_in with ⟨S, hS, hSk⟩
  refine ⟨S, hS, ?_⟩
  intro T hT
  have hT_card : T.card ∈ cards := ⟨T, hT, rfl⟩
  have h13 : T.card ≤ k := hk_max T.card hT_card
  rw [hSk] at *
  <;> exact h13

/-- Existence of a packing that is maximal by inclusion.

From a maximum-cardinality packing, we deduce that no additional center can be
added while preserving disjointness, since that would increase cardinality. -/
theorem exists_maximal_packing_max
    (A : Point 3 ≃ₗ[ℝ] Point 3) (η : ℝ) (hη : 0 < η)
    (h : scaledEllipsoid A (2 * η) 0 ⊆ unitBall 3) :
    ∃ (S : Finset (Point 3)),
      (∀ z ∈ S, ‖z‖ ≤ 1 / 2) ∧
      (∀ z ∈ S, scaledEllipsoid A η z ⊆ unitBall 3) ∧
      (↑S : Set (Point 3)).PairwiseDisjoint (fun z => scaledEllipsoid A η z) ∧
      (∀ (x : Point 3), ‖x‖ ≤ 1 / 2 →
        (∀ z ∈ S, Disjoint (scaledEllipsoid A η x) (scaledEllipsoid A η z)) → x ∈ S) := by
  rcases exists_maximal_packing A η hη h with ⟨S, hS, hS_max_card⟩
  have hS_centers : ∀ z ∈ S, ‖z‖ ≤ 1 / 2 := hS.1
  have hS_disjoint : (↑S : Set (Point 3)).PairwiseDisjoint (fun z => scaledEllipsoid A η z) := hS.2
  have hS_inball : ∀ z ∈ S, scaledEllipsoid A η z ⊆ unitBall 3 := by
    intro z hz
    exact center_containment A η hη z h (hS_centers z hz)
  have hS_maximal : ∀ (x : Point 3), ‖x‖ ≤ 1 / 2 →
      (∀ z ∈ S, Disjoint (scaledEllipsoid A η x) (scaledEllipsoid A η z)) → x ∈ S := by
    intro x hx_norm hx_disj
    by_contra hx_notin
    let S' := insert x S
    have hx_notin' : x ∉ S := hx_notin
    have hS'_centers : ∀ z ∈ S', ‖z‖ ≤ 1 / 2 := by
      intro z hz
      by_cases h : z = x
      · rw [h]; exact hx_norm
      · have hz' : z ∈ S := by
          simpa [S', h] using hz
        exact hS_centers z hz'
    have hS'_disjoint : (↑S' : Set (Point 3)).PairwiseDisjoint (fun z => scaledEllipsoid A η z) := by
      intro z1 hz1 z2 hz2 hne
      by_cases h1 : z1 = x
      · rw [h1]
        have h_z2_ne_x : z2 ≠ x := by
          intro h_eq; apply hne; rw [h1, h_eq]
        have hz2' : z2 ∈ S := by
          have h : z2 ∈ insert x S := hz2
          simpa [h_z2_ne_x] using h
        exact hx_disj z2 hz2'
      · by_cases h2 : z2 = x
        · rw [h2]
          have h_z1_ne_x : z1 ≠ x := by
            intro h_eq; apply hne; rw [h_eq, h2]
          have hz1' : z1 ∈ S := by
            have h : z1 ∈ insert x S := hz1
            simpa [h_z1_ne_x] using h
          exact (hx_disj z1 hz1').symm
        · have hz1' : z1 ∈ S := by
            have h : z1 ∈ insert x S := hz1
            simpa [h1] using h
          have hz2' : z2 ∈ S := by
            have h : z2 ∈ insert x S := hz2
            simpa [h2] using h
          exact hS_disjoint hz1' hz2' hne
    have hS'_packing : IsPacking A η S' := ⟨hS'_centers, hS'_disjoint⟩
    have h_card : S'.card = S.card + 1 := by
      simp [S', hx_notin']
      <;> omega
    have h_contra : S'.card ≤ S.card := hS_max_card S' hS'_packing
    rw [h_card] at h_contra
    <;> omega
  exact ⟨S, hS_centers, hS_inball, hS_disjoint, hS_maximal⟩

end Kakeya.CV

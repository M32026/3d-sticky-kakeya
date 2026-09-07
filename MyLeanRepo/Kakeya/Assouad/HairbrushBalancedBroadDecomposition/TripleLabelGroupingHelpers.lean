import MyLeanRepo.Kakeya.Assouad.Subunit.HairbrushStatements
import MyLeanRepo.Kakeya.Assouad.HairbrushBalancedBroadDecomposition.SlabGroupingHelpers
import MyLeanRepo.Kakeya.Assouad.HairbrushBalancedBroadDecomposition.SlabGeometryHelpers
import MyLeanRepo.Kakeya.Assouad.HairbrushBalancedBroadDecomposition.SlabVolumeBound
import MyLeanRepo.Kakeya.Streamlined.VolumeHelpers
import MyLeanRepo.Kakeya.Hairbrush.IntersectionSumBound.Preparations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Geometry.Euclidean.Angle.Unoriented.CrossProduct
import Mathlib.Data.Int.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic

/-!
# Helper lemmas for triple-label (direction + two transverse strips) incidence grouping

Provides:
1. Finite enumeration of nonempty `(direction-label, strip-index1, strip-index2)` triples.
2. Point witness that a triple belongs to the finite enumeration.
3. Measurability of triple assignment sets (intersection of two strip sets).
4. Tube occurrence bound: each tube appears in at most `1000 * 49 ≤ 1000000` groups.
5. Group union partition, label consistency for triple labels.
6. Convex container (intersection of two slabs + unit ball).
-/

noncomputable section

open MeasureTheory Metric Set Finset Real
open scoped Matrix

attribute [local instance] Classical.propDecidable

namespace Kakeya.Assouad

/-- Euclidean cross product local to the Appendix-B grouping geometry. -/
private def groupingCross (u v : Point3) : Point3 :=
  WithLp.toLp 2 ((u : Fin 3 → ℝ) ⨯₃ (v : Fin 3 → ℝ))

/-!
## Triple label enumeration
-/

/-- The finite set of all candidate `(label, strip1, strip2)` triples. -/
def allTripleLabels {labelCount : ℕ} (capRadius : ℝ) :
    Finset (Fin labelCount × ℤ × ℤ) :=
  Finset.biUnion (Finset.univ : Finset (Fin labelCount)) fun j =>
    (Finset.Icc (-(Int.ceil (1 / capRadius))) (Int.ceil (1 / capRadius))).biUnion
      fun k1 =>
        (Finset.Icc (-(Int.ceil (1 / capRadius))) (Int.ceil (1 / capRadius))).image
          (fun k2 : ℤ => (j, k1, k2))

/-- A point `x` with label `j` witnesses that its triple is in `allTripleLabels`. -/
lemma point_witnesses_triple {labelCount : ℕ} {capRadius : ℝ} (hcap_pos : 0 < capRadius)
    (n1 n2 : Fin labelCount → Point3)
    (hn1_unit : ∀ j, ‖n1 j‖ = 1) (hn2_unit : ∀ j, ‖n2 j‖ = 1)
    (label : Point3 → Fin labelCount) (S : Set Point3)
    (x : Point3) (_hxS : x ∈ S) (hx_ball : x ∈ Kakeya.DeltaTube.unitBall)
    (j : Fin labelCount) (_hj : label x = j) :
    (j, Int.floor (inner ℝ x (n1 j) / capRadius),
        Int.floor (inner ℝ x (n2 j) / capRadius)) ∈ allTripleLabels capRadius := by
  set k1 : ℤ := Int.floor (inner ℝ x (n1 j) / capRadius) with hk1_def
  set k2 : ℤ := Int.floor (inner ℝ x (n2 j) / capRadius) with hk2_def
  have h_k1_in : k1 ∈ Finset.Icc (-(Int.ceil (1 / capRadius))) (Int.ceil (1 / capRadius)) :=
    strip_index_in_range hx_ball (hn1_unit j) hcap_pos
  have h_k2_in : k2 ∈ Finset.Icc (-(Int.ceil (1 / capRadius))) (Int.ceil (1 / capRadius)) :=
    strip_index_in_range hx_ball (hn2_unit j) hcap_pos
  have h_inner : (j, k1, k2) ∈ (Finset.Icc (-(Int.ceil (1 / capRadius))) (Int.ceil (1 / capRadius))).biUnion
      (fun k1 : ℤ => (Finset.Icc (-(Int.ceil (1 / capRadius))) (Int.ceil (1 / capRadius))).image
        (fun k2 : ℤ => (j, k1, k2))) := by
    rw [Finset.mem_biUnion]
    refine ⟨k1, h_k1_in, ?_⟩
    rw [Finset.mem_image]
    exact ⟨k2, h_k2_in, rfl⟩
  rw [allTripleLabels, Finset.mem_biUnion]
  exact ⟨j, by simp, h_inner⟩

/-- Filter to only nonempty triples. -/
def nonemptyTripleLabels {labelCount : ℕ} {capRadius : ℝ}
    (n1 n2 : Fin labelCount → Point3)
    (label : Point3 → Fin labelCount)
    (S : Set Point3) : Finset (Fin labelCount × ℤ × ℤ) :=
  (allTripleLabels capRadius).filter fun p =>
    (S ∩ {x | label x = p.1 ∧
      Int.floor (inner ℝ x (n1 p.1) / capRadius) = p.2.1 ∧
      Int.floor (inner ℝ x (n2 p.1) / capRadius) = p.2.2}).Nonempty

/-- If `S` is nonempty and contained in the unit ball, then `nonemptyTripleLabels` is nonempty. -/
lemma nonemptyTripleLabels_nonempty {labelCount : ℕ} {capRadius : ℝ}
    (hcap_pos : 0 < capRadius)
    (n1 n2 : Fin labelCount → Point3)
    (hn1_unit : ∀ j, ‖n1 j‖ = 1) (hn2_unit : ∀ j, ‖n2 j‖ = 1)
    (label : Point3 → Fin labelCount)
    (S : Set Point3) (hS_sub_ball : S ⊆ Kakeya.DeltaTube.unitBall)
    (hS_nonempty : S.Nonempty) :
    (nonemptyTripleLabels (capRadius := capRadius) n1 n2 label S).Nonempty := by
  rcases hS_nonempty with ⟨x, hxS⟩
  let j := label x
  let k1 := Int.floor (inner ℝ x (n1 j) / capRadius)
  let k2 := Int.floor (inner ℝ x (n2 j) / capRadius)
  have hx_ball : x ∈ Kakeya.DeltaTube.unitBall := hS_sub_ball hxS
  have h_triple_in_all : (j, k1, k2) ∈ allTripleLabels capRadius :=
    point_witnesses_triple hcap_pos n1 n2 hn1_unit hn2_unit label S x hxS hx_ball j rfl
  have h_witness : x ∈ S ∩ {x : Point3 | label x = j ∧
      Int.floor (inner ℝ x (n1 j) / capRadius) = k1 ∧
      Int.floor (inner ℝ x (n2 j) / capRadius) = k2} := by
    exact ⟨hxS, by simp [j, k1, k2]⟩
  have h_nonempty : (S ∩ {x : Point3 | label x = j ∧
      Int.floor (inner ℝ x (n1 j) / capRadius) = k1 ∧
      Int.floor (inner ℝ x (n2 j) / capRadius) = k2}).Nonempty :=
    ⟨x, h_witness⟩
  have h_in_filter : (j, k1, k2) ∈
      nonemptyTripleLabels (capRadius := capRadius) n1 n2 label S := by
    rw [nonemptyTripleLabels, Finset.mem_filter]
    exact ⟨h_triple_in_all, h_nonempty⟩
  exact ⟨(j, k1, k2), h_in_filter⟩

/-!
## Measurability of triple assignment sets
-/

/-- The set of points whose two transverse strip indices equal `(k1, k2)` is measurable. -/
lemma measurable_triple_set {n1 n2 : Point3} {w : ℝ} (k1 k2 : ℤ) :
    MeasurableSet {x : Point3 | Int.floor (inner ℝ x n1 / w) = k1 ∧
                                 Int.floor (inner ℝ x n2 / w) = k2} := by
  have h1 : MeasurableSet {x : Point3 | Int.floor (inner ℝ x n1 / w) = k1} :=
    measurable_strip_set k1
  have h2 : MeasurableSet {x : Point3 | Int.floor (inner ℝ x n2 / w) = k2} :=
    measurable_strip_set k2
  have h_eq : {x : Point3 | Int.floor (inner ℝ x n1 / w) = k1 ∧
                            Int.floor (inner ℝ x n2 / w) = k2} =
      {x : Point3 | Int.floor (inner ℝ x n1 / w) = k1} ∩
      {x : Point3 | Int.floor (inner ℝ x n2 / w) = k2} := by
    ext x; simp
  rw [h_eq]
  exact h1.inter h2

/-!
## Tube occurrence bound for triple labels

For each tube T:
- At most 1000 direction labels can appear on T.
- For each direction label j, both projections have diameter ≤ 3*capRadius,
  so each has at most 7 strip indices.
- Total: ≤ 1000 * 7 * 7 = 49000 groups per tube, well under 1000000.
-/

lemma tube_occurrence_bound_triple
    {δ : ℝ} {F : Kakeya.TubeFamily δ}
    {Y : Kakeya.Shading F}
    {labelCount : ℕ}
    {label : Point3 → Fin labelCount}
    {center : Fin labelCount → Point3}
    {capRadius : ℝ}
    (hδ : 0 < δ) (hcap : δ ≤ capRadius) (hcap1 : capRadius ≤ 1)
    (hcenter_unit : ∀ j, ‖center j‖ = 1)
    (n1 n2 : Fin labelCount → Point3)
    (hn1_unit : ∀ j, ‖n1 j‖ = 1) (hn2_unit : ∀ j, ‖n2 j‖ = 1)
    (hn1_orth : ∀ j, inner ℝ (center j) (n1 j) = 0)
    (hn2_orth : ∀ j, inner ℝ (center j) (n2 j) = 0)
    (h_pointwise : ∀ x ∈ Y.union, ∀ T ∈ F, x ∈ Y.carrier T →
        hairbrushAcuteDirectionAngle T.direction (center (label x)) ≤ capRadius)
    (h_label_overlap : ∀ T ∈ F,
        ((Finset.univ.filter fun j : Fin labelCount =>
            ∃ x ∈ Y.carrier T, label x = j).card : ENNReal) ≤ 1000)
    (groups : Finset (Fin labelCount × ℤ × ℤ))
    (family : (Fin labelCount × ℤ × ℤ) → Kakeya.TubeFamily δ)
    (h_family_def : ∀ p, family p = F.filter (fun T =>
        ∃ x ∈ Y.carrier T, label x = p.1 ∧
          Int.floor (inner ℝ x (n1 p.1) / capRadius) = p.2.1 ∧
          Int.floor (inner ℝ x (n2 p.1) / capRadius) = p.2.2)) :
    ∑ p ∈ groups, (family p).enncard ≤ 1000000 * F.enncard := by
  have hcap_pos : 0 < capRadius := by linarith
  have h_main : ∀ T ∈ F, (groups.filter (fun p => T ∈ family p)).card ≤ 49000 := by
    intro T hT
    let J_T : Finset (Fin labelCount) :=
      Finset.univ.filter (fun j => ∃ x ∈ Y.carrier T, label x = j)
    have hJ_card : (J_T.card : ENNReal) ≤ 1000 := h_label_overlap T hT
    have hJ_card' : J_T.card ≤ 1000 := by exact_mod_cast hJ_card
    have h_witness : ∀ j ∈ J_T, ∃ (x : Point3), x ∈ Y.carrier T ∧ label x = j := by
      intro j hj
      simp only [J_T, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      exact hj
    let xfunc : Fin labelCount → Point3 := fun j =>
      if hj : j ∈ J_T then Classical.choose (h_witness j hj) else 0
    have hx1 : ∀ j ∈ J_T, xfunc j ∈ Y.carrier T := by
      intro j hj
      dsimp only [xfunc]
      rw [dif_pos hj]
      exact (Classical.choose_spec (h_witness j hj)).1
    have hx2 : ∀ j ∈ J_T, label (xfunc j) = j := by
      intro j hj
      dsimp only [xfunc]
      rw [dif_pos hj]
      exact (Classical.choose_spec (h_witness j hj)).2
    let K1 (j : Fin labelCount) : Finset ℤ :=
      Finset.Icc (Int.floor (inner ℝ (xfunc j) (n1 j) / capRadius) - 3)
                (Int.floor (inner ℝ (xfunc j) (n1 j) / capRadius) + 3)
    let K2 (j : Fin labelCount) : Finset ℤ :=
      Finset.Icc (Int.floor (inner ℝ (xfunc j) (n2 j) / capRadius) - 3)
                (Int.floor (inner ℝ (xfunc j) (n2 j) / capRadius) + 3)
    have hK1_card : ∀ j ∈ J_T, (K1 j).card ≤ 7 := by
      intro j _
      simp [K1] <;> omega
    have hK2_card : ∀ j ∈ J_T, (K2 j).card ≤ 7 := by
      intro j _
      simp [K2] <;> omega
    have h_include : ∀ (p : Fin labelCount × ℤ × ℤ), T ∈ family p →
        p.1 ∈ J_T ∧ p.2.1 ∈ K1 p.1 ∧ p.2.2 ∈ K2 p.1 := by
      rintro ⟨j, k1, k2⟩ hTp
      have h_exists : ∃ (x : Point3), x ∈ Y.carrier T ∧ label x = j ∧
          Int.floor (inner ℝ x (n1 j) / capRadius) = k1 ∧
          Int.floor (inner ℝ x (n2 j) / capRadius) = k2 := by
        rw [h_family_def (j, k1, k2)] at hTp
        simp only [Finset.mem_filter] at hTp
        exact hTp.2
      rcases h_exists with ⟨x, hxY, hlabel, hstrip1, hstrip2⟩
      have hj_J : j ∈ J_T := by
        simp only [J_T, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨x, hxY, hlabel⟩
      have h_x_in_T : x ∈ T.carrier := Y.subset_tube hT hxY
      have h_xj_in_T : xfunc j ∈ T.carrier := Y.subset_tube hT (hx1 j hj_J)
      have h_xj_union : xfunc j ∈ Y.union := by
        exact ⟨T, hT, hx1 j hj_J⟩
      have h_angle : hairbrushAcuteDirectionAngle T.direction (center j) ≤ capRadius := by
        have h := h_pointwise (xfunc j) h_xj_union T hT (hx1 j hj_J)
        have hlabel_j : label (xfunc j) = j := hx2 j hj_J
        rw [hlabel_j] at h
        exact h
      have h_proj_var1 : |inner ℝ x (n1 j) - inner ℝ (xfunc j) (n1 j)| ≤ capRadius + 2 * δ :=
        tube_projection_variation hδ hcap hcap1 T (center j) (n1 j)
          (hcenter_unit j) (hn1_unit j) (hn1_orth j) h_angle x (xfunc j) h_x_in_T h_xj_in_T
      have h_proj_var2 : |inner ℝ x (n2 j) - inner ℝ (xfunc j) (n2 j)| ≤ capRadius + 2 * δ :=
        tube_projection_variation hδ hcap hcap1 T (center j) (n2 j)
          (hcenter_unit j) (hn2_unit j) (hn2_orth j) h_angle x (xfunc j) h_x_in_T h_xj_in_T
      have h_abs1 : |inner ℝ x (n1 j) / capRadius - inner ℝ (xfunc j) (n1 j) / capRadius| ≤ 3 := by
        have h41 : |inner ℝ x (n1 j) - inner ℝ (xfunc j) (n1 j)| ≤ capRadius + 2 * δ := h_proj_var1
        have h42 : |inner ℝ x (n1 j) - inner ℝ (xfunc j) (n1 j)| / capRadius ≤ (capRadius + 2 * δ) / capRadius :=
          div_le_div_of_nonneg_right h41 (by linarith)
        have h43 : (capRadius + 2 * δ) / capRadius ≤ 3 := by
          have h44 : capRadius + 2 * δ ≤ 3 * capRadius := by linarith [hcap]
          have h45 : (capRadius + 2 * δ) / capRadius ≤ (3 * capRadius) / capRadius :=
            div_le_div_of_nonneg_right h44 (by linarith)
          have h46 : (3 * capRadius) / capRadius = 3 := by
            field_simp [hcap_pos.ne'] <;> ring
          rw [h46] at h45
          exact h45
        have h47 : |(inner ℝ x (n1 j) - inner ℝ (xfunc j) (n1 j)) / capRadius| ≤ 3 := by
          rw [abs_div, abs_of_pos hcap_pos]
          exact le_trans h42 h43
        have h5 : (inner ℝ x (n1 j) - inner ℝ (xfunc j) (n1 j)) / capRadius =
            inner ℝ x (n1 j) / capRadius - inner ℝ (xfunc j) (n1 j) / capRadius := by ring
        rw [h5] at h47
        exact h47
      have h_abs2 : |inner ℝ x (n2 j) / capRadius - inner ℝ (xfunc j) (n2 j) / capRadius| ≤ 3 := by
        have h41 : |inner ℝ x (n2 j) - inner ℝ (xfunc j) (n2 j)| ≤ capRadius + 2 * δ := h_proj_var2
        have h42 : |inner ℝ x (n2 j) - inner ℝ (xfunc j) (n2 j)| / capRadius ≤ (capRadius + 2 * δ) / capRadius :=
          div_le_div_of_nonneg_right h41 (by linarith)
        have h43 : (capRadius + 2 * δ) / capRadius ≤ 3 := by
          have h44 : capRadius + 2 * δ ≤ 3 * capRadius := by linarith [hcap]
          have h45 : (capRadius + 2 * δ) / capRadius ≤ (3 * capRadius) / capRadius :=
            div_le_div_of_nonneg_right h44 (by linarith)
          have h46 : (3 * capRadius) / capRadius = 3 := by
            field_simp [hcap_pos.ne'] <;> ring
          rw [h46] at h45
          exact h45
        have h47 : |(inner ℝ x (n2 j) - inner ℝ (xfunc j) (n2 j)) / capRadius| ≤ 3 := by
          rw [abs_div, abs_of_pos hcap_pos]
          exact le_trans h42 h43
        have h5 : (inner ℝ x (n2 j) - inner ℝ (xfunc j) (n2 j)) / capRadius =
            inner ℝ x (n2 j) / capRadius - inner ℝ (xfunc j) (n2 j) / capRadius := by ring
        rw [h5] at h47
        exact h47
      have h_floor1 : |(Int.floor (inner ℝ x (n1 j) / capRadius) : ℤ) -
          (Int.floor (inner ℝ (xfunc j) (n1 j) / capRadius) : ℤ)| ≤ 3 :=
        abs_floor_sub_le h_abs1
      have h_floor2 : |(Int.floor (inner ℝ x (n2 j) / capRadius) : ℤ) -
          (Int.floor (inner ℝ (xfunc j) (n2 j) / capRadius) : ℤ)| ≤ 3 :=
        abs_floor_sub_le h_abs2
      rw [hstrip1] at h_floor1
      rw [hstrip2] at h_floor2
      have h_bounds1 : -3 ≤ k1 - Int.floor (inner ℝ (xfunc j) (n1 j) / capRadius) ∧
          k1 - Int.floor (inner ℝ (xfunc j) (n1 j) / capRadius) ≤ 3 := abs_le.mp h_floor1
      have h_bounds2 : -3 ≤ k2 - Int.floor (inner ℝ (xfunc j) (n2 j) / capRadius) ∧
          k2 - Int.floor (inner ℝ (xfunc j) (n2 j) / capRadius) ≤ 3 := abs_le.mp h_floor2
      have h21 : k1 ∈ K1 j := by
        rw [Finset.mem_Icc]
        exact ⟨by linarith, by linarith⟩
      have h22 : k2 ∈ K2 j := by
        rw [Finset.mem_Icc]
        exact ⟨by linarith, by linarith⟩
      exact ⟨hj_J, h21, h22⟩
    let S_T : Finset (Fin labelCount × ℤ × ℤ) :=
      Finset.biUnion J_T (fun j =>
        (K1 j).biUnion (fun k1 =>
          (K2 j).image (fun k2 : ℤ => (j, k1, k2))))
    have h_subset : groups.filter (fun p => T ∈ family p) ⊆ S_T := by
      intro p hp
      have hTp : T ∈ family p := (Finset.mem_filter.mp hp).2
      have h1 : p.1 ∈ J_T ∧ p.2.1 ∈ K1 p.1 ∧ p.2.2 ∈ K2 p.1 := h_include p hTp
      have h2 : p ∈ S_T := by
        rw [Finset.mem_biUnion]
        refine ⟨p.1, h1.1, ?_⟩
        rw [Finset.mem_biUnion]
        refine ⟨p.2.1, h1.2.1, ?_⟩
        rw [Finset.mem_image]
        refine ⟨p.2.2, h1.2.2, ?_⟩
        simp
      exact h2
    calc
      (groups.filter (fun p => T ∈ family p)).card
        ≤ S_T.card := Finset.card_le_card h_subset
      _ ≤ ∑ j ∈ J_T, ((K1 j).biUnion (fun k1 => (K2 j).image (fun k2 : ℤ => (j, k1, k2)))).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ j ∈ J_T, (K1 j).card * (K2 j).card := by
          apply Finset.sum_le_sum
          intro j _
          calc
            ((K1 j).biUnion (fun k1 => (K2 j).image (fun k2 : ℤ => (j, k1, k2)))).card
              ≤ ∑ k1 ∈ K1 j, ((K2 j).image (fun k2 : ℤ => (j, k1, k2))).card :=
                Finset.card_biUnion_le
            _ ≤ ∑ k1 ∈ K1 j, (K2 j).card := by
                apply Finset.sum_le_sum
                intro _ _
                exact Finset.card_image_le
            _ = (K1 j).card * (K2 j).card := by
                rw [Finset.sum_const] <;> ring
      _ ≤ ∑ j ∈ J_T, 7 * 7 := by
          apply Finset.sum_le_sum
          intro j hj
          have h1 : (K1 j).card ≤ 7 := hK1_card j hj
          have h2 : (K2 j).card ≤ 7 := hK2_card j hj
          gcongr
      _ = 49 * J_T.card := by
          simp [Finset.sum_const] <;> ring
      _ ≤ 49 * 1000 := by gcongr
      _ = 49000 := by norm_num
  have h1 : ∀ p ∈ groups, family p ⊆ F := by
    intro p _
    rw [h_family_def p]
    exact Finset.filter_subset _ _
  have h_double_count : ∑ p ∈ groups, (family p).enncard =
      ∑ T ∈ F, ↑((groups.filter (fun p => T ∈ family p)).card) := by
    calc
      ∑ p ∈ groups, (family p).enncard
        = ∑ p ∈ groups, ∑ T ∈ family p, (1 : ENNReal) := by
          apply Finset.sum_congr rfl
          intro p _
          simp [Kakeya.TubeFamily.enncard]
      _ = ∑ p ∈ groups, ∑ T ∈ F, if T ∈ family p then (1 : ENNReal) else 0 := by
          apply Finset.sum_congr rfl
          intro p hp
          have h2 : family p ⊆ F := h1 p hp
          rw [Finset.sum_ite]
          <;> simp [h2]
      _ = ∑ T ∈ F, ∑ p ∈ groups, if T ∈ family p then (1 : ENNReal) else 0 := by
          rw [Finset.sum_comm]
      _ = ∑ T ∈ F, ↑((groups.filter (fun p => T ∈ family p)).card) := by
          apply Finset.sum_congr rfl
          intro T _
          simp [Finset.filter]
  rw [h_double_count]
  calc
    ∑ T ∈ F, ↑((groups.filter (fun p => T ∈ family p)).card)
      ≤ ∑ T ∈ F, (49000 : ENNReal) := by
        apply Finset.sum_le_sum
        intro T hT
        exact_mod_cast h_main T hT
    _ = 49000 * F.enncard := by
        simp [Kakeya.TubeFamily.enncard, Finset.sum_const]
        <;> ring
    _ ≤ 1000000 * F.enncard := by
        gcongr
        <;> norm_num

/-!
## Group union partition for triple labels
-/

/-- Group unions form a partition of the original shading union for triple labels. -/
lemma group_union_partition_triple
    {δ : ℝ} {F : Kakeya.TubeFamily δ} {Y : Kakeya.Shading F}
    {labelCount : ℕ} {label : Point3 → Fin labelCount}
    (n1 n2 : Fin labelCount → Point3) (capRadius : ℝ)
    (groups : Finset (Fin labelCount × ℤ × ℤ))
    (pointLabel : Point3 → Fin labelCount × ℤ × ℤ)
    (h_groups_complete : ∀ x ∈ Y.union, pointLabel x ∈ groups)
    (family : (Fin labelCount × ℤ × ℤ) → Kakeya.TubeFamily δ)
    (shading : ∀ p, Kakeya.Shading (family p))
    (h_shading_def : ∀ p T, T ∈ family p →
        (shading p).carrier T = Y.carrier T ∩ {x | pointLabel x = p})
    (h_family_def : ∀ p, family p = F.filter (fun T =>
        ∃ x ∈ Y.carrier T, pointLabel x = p)) :
    (∀ p q, p ≠ q → Disjoint (shading p).union (shading q).union) ∧
    (⋃ p ∈ groups, (shading p).union) = Y.union := by
  have h_family_sub : ∀ p, family p ⊆ F := by
    intro p
    rw [h_family_def p]
    exact Finset.filter_subset _ _
  have h_disj : ∀ p q, p ≠ q → Disjoint (shading p).union (shading q).union := by
    intro p q hne
    rw [Set.disjoint_left]
    intro x hxp hxq
    rcases Set.mem_setOf.mp hxp with ⟨T, hTp, hxTp⟩
    have h1 : pointLabel x = p := by
      have h_eq : (shading p).carrier T = Y.carrier T ∩ {x | pointLabel x = p} :=
        h_shading_def p T hTp
      rw [h_eq] at hxTp
      exact hxTp.2
    rcases Set.mem_setOf.mp hxq with ⟨U, hUq, hxUq⟩
    have h2 : pointLabel x = q := by
      have h_eq : (shading q).carrier U = Y.carrier U ∩ {x | pointLabel x = q} :=
        h_shading_def q U hUq
      rw [h_eq] at hxUq
      exact hxUq.2
    have h3 : p = q := by
      have h4 : pointLabel x = p := h1
      have h5 : pointLabel x = q := h2
      rw [h4] at h5
      exact h5
    exact hne h3
  have h_subset : (⋃ p ∈ groups, (shading p).union) ⊆ Y.union := by
    intro x hx
    have h_ex : ∃ (p : Fin labelCount × ℤ × ℤ), p ∈ groups ∧ x ∈ (shading p).union := by
      simpa [Set.mem_biUnion] using hx
    rcases h_ex with ⟨p, hp, hxp⟩
    rcases Set.mem_setOf.mp hxp with ⟨T, hTp, hxTp⟩
    have hT_F : T ∈ F := h_family_sub p hTp
    have h_eq : (shading p).carrier T = Y.carrier T ∩ {x | pointLabel x = p} :=
      h_shading_def p T hTp
    rw [h_eq] at hxTp
    exact Set.mem_setOf.mpr ⟨T, hT_F, hxTp.1⟩
  have h_superset : Y.union ⊆ (⋃ p ∈ groups, (shading p).union) := by
    intro x hx
    rcases Set.mem_setOf.mp hx with ⟨T, hT_F, hxT⟩
    let p := pointLabel x
    have hp_in : p ∈ groups := h_groups_complete x hx
    have hT_in_family : T ∈ family p := by
      rw [h_family_def p, Finset.mem_filter]
      exact ⟨hT_F, ⟨x, hxT, rfl⟩⟩
    have h_x_in_carrier : x ∈ (shading p).carrier T := by
      have h_eq : (shading p).carrier T = Y.carrier T ∩ {x | pointLabel x = p} :=
        h_shading_def p T hT_in_family
      rw [h_eq]
      exact ⟨hxT, rfl⟩
    have h_x_in_union : x ∈ (shading p).union :=
      Set.mem_setOf.mpr ⟨T, hT_in_family, h_x_in_carrier⟩
    have h_goal : x ∈ (⋃ p ∈ groups, (shading p).union) := by
      simp only [Set.mem_iUnion]
      exact ⟨p, hp_in, h_x_in_union⟩
    exact h_goal
  have h_eq : (⋃ p ∈ groups, (shading p).union) = Y.union :=
    Set.Subset.antisymm h_subset h_superset
  exact ⟨h_disj, h_eq⟩

/-!
## Label consistency for triple labels
-/

/-- Label consistency for a triple-label incidence group. -/
lemma group_label_consistency_triple
    {δ : ℝ} {F : Kakeya.TubeFamily δ} {Y : Kakeya.Shading F}
    {labelCount : ℕ} {label : Point3 → Fin labelCount}
    (n1 n2 : Fin labelCount → Point3) (capRadius : ℝ)
    (pointLabel : Point3 → Fin labelCount × ℤ × ℤ)
    (hpointLabel_def : ∀ x, pointLabel x =
        (label x, Int.floor (inner ℝ x (n1 (label x)) / capRadius),
                   Int.floor (inner ℝ x (n2 (label x)) / capRadius)))
    (p : Fin labelCount × ℤ × ℤ)
    (family_p : Kakeya.TubeFamily δ)
    (shading_p : Kakeya.Shading family_p)
    (h_shading_def : ∀ T ∈ family_p,
        shading_p.carrier T = Y.carrier T ∩ {x | pointLabel x = p}) :
    ∀ T, ∀ hT : T ∈ family_p, ∀ x ∈ shading_p.carrier T,
      label x = p.1 := by
  intro T hT x hx
  have h1 : x ∈ {x : Point3 | pointLabel x = p} := by
    have h2 : x ∈ shading_p.carrier T := hx
    rw [h_shading_def T hT] at h2
    exact h2.2
  have h3 : pointLabel x = p := h1
  have h4 : pointLabel x = (label x, Int.floor (inner ℝ x (n1 (label x)) / capRadius),
                                     Int.floor (inner ℝ x (n2 (label x)) / capRadius)) :=
    hpointLabel_def x
  rw [h4] at h3
  simpa using congr_arg Prod.fst h3

/-!
## Convex container for triple-label groups

A group lies in the intersection of two slabs (one for each transverse direction)
and the unit ball. This is a convex set.
-/

/-- A slab carrier is convex.

The slab carrier is the intersection of the unit ball and the set
`{x | |inner x n - offset| ≤ radius}`, which is an intersection of
two half-spaces and hence convex. -/
lemma slab_carrier_convex (S : Kakeya.Slab) : Convex ℝ S.carrier := by
  have h1 : Convex ℝ Kakeya.DeltaTube.unitBall := convex_closedBall (0 : Point3) 1
  let f : Point3 →ₗ[ℝ] ℝ :=
    { toFun := fun x => inner ℝ x S.normal
      map_add' := by intro x y; simp [inner_add_left] <;> ring
      map_smul' := by intro c x; simp [inner_smul_left] <;> ring }
  have h_Icc_convex : Convex ℝ (Set.Icc (S.offset - S.radius) (S.offset + S.radius)) := convex_Icc _ _
  have h2 : Convex ℝ (f ⁻¹' (Set.Icc (S.offset - S.radius) (S.offset + S.radius))) :=
    h_Icc_convex.linear_preimage f
  have h_set_eq : f ⁻¹' (Set.Icc (S.offset - S.radius) (S.offset + S.radius)) =
      {x : Point3 | |inner ℝ x S.normal - S.offset| ≤ S.radius} := by
    ext x
    simp only [f, Set.mem_preimage, Set.mem_Icc, Set.mem_setOf_eq]
    have h : |inner ℝ x S.normal - S.offset| ≤ S.radius ↔
        S.offset - S.radius ≤ inner ℝ x S.normal ∧ inner ℝ x S.normal ≤ S.offset + S.radius := by
      constructor
      · intro h4
        have h5 : -(S.radius) ≤ inner ℝ x S.normal - S.offset := (abs_le.mp h4).1
        have h6 : inner ℝ x S.normal - S.offset ≤ S.radius := (abs_le.mp h4).2
        exact ⟨by linarith, by linarith⟩
      · rintro ⟨h5, h6⟩
        have h7 : -(S.radius) ≤ inner ℝ x S.normal - S.offset := by linarith
        have h8 : inner ℝ x S.normal - S.offset ≤ S.radius := by linarith
        exact abs_le.mpr ⟨h7, h8⟩
    exact h.symm
  have h2' : Convex ℝ {x : Point3 | |inner ℝ x S.normal - S.offset| ≤ S.radius} := by
    convert h2 using 1
    exact h_set_eq.symm
  have h3 : S.carrier = Kakeya.DeltaTube.unitBall ∩
      {x : Point3 | |inner ℝ x S.normal - S.offset| ≤ S.radius} := by
    ext x
    simp only [Kakeya.Slab.carrier, Set.mem_inter_iff, Set.mem_setOf_eq]
    have h_H_nonempty : S.hyperplane.Nonempty := by
      have hinner_n : inner ℝ S.normal S.normal = (1 : ℝ) := by
        have h : inner ℝ S.normal S.normal = ‖S.normal‖ ^ 2 := real_inner_self_eq_norm_sq S.normal
        rw [h, S.normal_unit] <;> norm_num
      have h_off : inner ℝ (S.offset • S.normal) S.normal = S.offset := by
        have h1 : inner ℝ (S.offset • S.normal) S.normal = S.offset * inner ℝ S.normal S.normal := by
          simp [inner_smul_left]
        rw [h1, hinner_n] <;> ring
      refine ⟨S.offset • S.normal, ?_⟩
      simpa [Kakeya.Slab.hyperplane] using h_off
    have h_dist_eq : Metric.infDist x S.hyperplane = |inner ℝ x S.normal - S.offset| := by
      have h_hyperplane : S.hyperplane = {z : Point3 | inner ℝ z S.normal = S.offset} := by
        ext z; simp [Kakeya.Slab.hyperplane] <;> rfl
      rw [h_hyperplane]; exact dist_to_hyperplane S.normal_unit
    have h_radius_nonneg : 0 ≤ S.radius := S.radius_nonneg
    have h_edist : ENNReal.ofReal (Metric.infDist x S.hyperplane) = Metric.infEDist x S.hyperplane := by
      rw [← ENNReal.ofReal_toReal (Metric.infEDist_ne_top h_H_nonempty)] <;> rfl
    have h_cthick : x ∈ Metric.cthickening S.radius S.hyperplane ↔
        Metric.infDist x S.hyperplane ≤ S.radius := by
      rw [Metric.mem_cthickening_iff, ←h_edist]
      rw [ENNReal.ofReal_le_ofReal_iff h_radius_nonneg]
    rw [h_cthick, h_dist_eq]
    <;> rfl
  rw [h3]
  exact h1.inter h2'

/-- Intersection of two slabs and the unit ball is convex. -/
lemma convex_container_intersection
    (S1 S2 : Kakeya.Slab) :
    Convex ℝ (S1.carrier ∩ S2.carrier ∩ Kakeya.DeltaTube.unitBall) := by
  have h1 : Convex ℝ S1.carrier := slab_carrier_convex S1
  have h2 : Convex ℝ S2.carrier := slab_carrier_convex S2
  have h3 : Convex ℝ Kakeya.DeltaTube.unitBall := convex_closedBall (0 : Point3) 1
  have h4 : Convex ℝ (S1.carrier ∩ S2.carrier ∩ Kakeya.DeltaTube.unitBall) := by
    convert h1.inter (h2.inter h3) using 1
    <;> ext x <;> simp [Set.mem_inter_iff] <;> tauto
  exact h4

/-- Given a unit vector `v`, extend it to an orthonormal frame `(v, n1, n2)`.

Uses `exists_perp_unit` to find `n1`, then takes their Euclidean cross product.
The cross product is perpendicular to both arguments and has norm 1
when the inputs are orthonormal. -/
lemma exists_orthonormal_frame (v : Point3) (hv : ‖v‖ = 1) :
    ∃ (n1 n2 : Point3), ‖n1‖ = 1 ∧ ‖n2‖ = 1 ∧
      inner ℝ v n1 = 0 ∧ inner ℝ v n2 = 0 ∧ inner ℝ n1 n2 = 0 := by
  rcases exists_perp_unit v hv with ⟨n1, hn1, horth1⟩
  let n2 : Point3 := groupingCross v n1
  have hcross_def : (n2 : Fin 3 → ℝ) = (v : Fin 3 → ℝ) ⨯₃ (n1 : Fin 3 → ℝ) := by rfl
  have hinner_v_n2 : inner ℝ v n2 = 0 := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    have hstar : star (v : Fin 3 → ℝ) = (v : Fin 3 → ℝ) := by ext i; simp
    rw [hstar, hcross_def, dotProduct_comm]
    exact dot_self_cross (v : Fin 3 → ℝ) (n1 : Fin 3 → ℝ)
  have hinner_n1_n2 : inner ℝ n1 n2 = 0 := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    have hstar : star (n1 : Fin 3 → ℝ) = (n1 : Fin 3 → ℝ) := by ext i; simp
    rw [hstar, hcross_def, dotProduct_comm]
    exact dot_cross_self (v : Fin 3 → ℝ) (n1 : Fin 3 → ℝ)
  have hsin : Real.sin (InnerProductGeometry.angle v n1) = 1 := by
    have h1 : Real.sin (InnerProductGeometry.angle v n1) * (‖v‖ * ‖n1‖) =
        Real.sqrt (inner ℝ v v * inner ℝ n1 n1 - inner ℝ v n1 * inner ℝ v n1) :=
      InnerProductGeometry.sin_angle_mul_norm_mul_norm v n1
    have h2 : inner ℝ v v = 1 := by
      have h : inner ℝ v v = ‖v‖ ^ 2 := real_inner_self_eq_norm_sq v
      rw [h, hv] <;> norm_num
    have h3 : inner ℝ n1 n1 = 1 := by
      have h : inner ℝ n1 n1 = ‖n1‖ ^ 2 := real_inner_self_eq_norm_sq n1
      rw [h, hn1] <;> norm_num
    rw [h2, h3, horth1] at h1
    have h4 : Real.sin (InnerProductGeometry.angle v n1) * (‖v‖ * ‖n1‖) = 1 := by
      rw [h1] <;> norm_num
    have h5 : ‖v‖ * ‖n1‖ = 1 := by rw [hv, hn1] <;> norm_num
    rw [h5] at h4
    linarith
  have hnorm_n2 : ‖n2‖ = 1 := by
    have h6 : ‖n2‖ = ‖v‖ * ‖n1‖ * Real.sin (InnerProductGeometry.angle v n1) :=
      InnerProductGeometry.norm_toLp_symm_crossProduct (v : Fin 3 → ℝ) (n1 : Fin 3 → ℝ)
    rw [h6, hv, hn1, hsin] <;> norm_num
  exact ⟨n1, n2, hn1, hnorm_n2, horth1, hinner_v_n2, hinner_n1_n2⟩

/-- Volume of the intersection of two transverse slabs.

Given two slabs whose normals are orthonormal, the intersection is contained
in a box of dimensions `2*r1 × 2*r2 × 2` after an orthonormal coordinate change.
Hence its volume is at most `8 * r1 * r2`. -/
lemma two_strip_container_volume (S1 S2 : Kakeya.Slab)
    (hn_orth : inner ℝ S1.normal S2.normal = 0)
    {capRadius : ℝ} (hcap_pos : 0 < capRadius)
    (hr1 : S1.radius ≤ 10 * capRadius)
    (hr2 : S2.radius ≤ 10 * capRadius) :
    volume (S1.carrier ∩ S2.carrier) ≤ ENNReal.ofReal (1000000 * capRadius ^ 2) := by
  set n1 : Point3 := S1.normal with hn1_def
  set n2 : Point3 := S2.normal with hn2_def
  have hn1 : ‖n1‖ = 1 := S1.normal_unit
  have hn2 : ‖n2‖ = 1 := S2.normal_unit
  set v : Point3 := groupingCross n1 n2 with hv_def
  have hcross_def : (v : Fin 3 → ℝ) = (n1 : Fin 3 → ℝ) ⨯₃ (n2 : Fin 3 → ℝ) := by rfl
  have hinner_n1_v : inner ℝ n1 v = 0 := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    have hstar : star (n1 : Fin 3 → ℝ) = (n1 : Fin 3 → ℝ) := by ext i; simp
    rw [hstar, hcross_def, dotProduct_comm]
    exact dot_self_cross (n1 : Fin 3 → ℝ) (n2 : Fin 3 → ℝ)
  have hinner_n2_v : inner ℝ n2 v = 0 := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    have hstar : star (n2 : Fin 3 → ℝ) = (n2 : Fin 3 → ℝ) := by ext i; simp
    rw [hstar, hcross_def, dotProduct_comm]
    exact dot_cross_self (n1 : Fin 3 → ℝ) (n2 : Fin 3 → ℝ)
  have hsin : Real.sin (InnerProductGeometry.angle n1 n2) = 1 := by
    have h1 : Real.sin (InnerProductGeometry.angle n1 n2) * (‖n1‖ * ‖n2‖) =
        Real.sqrt (inner ℝ n1 n1 * inner ℝ n2 n2 - inner ℝ n1 n2 * inner ℝ n1 n2) :=
      InnerProductGeometry.sin_angle_mul_norm_mul_norm n1 n2
    have h2 : inner ℝ n1 n1 = 1 := by
      have h : inner ℝ n1 n1 = ‖n1‖ ^ 2 := real_inner_self_eq_norm_sq n1
      rw [h, hn1] <;> norm_num
    have h3 : inner ℝ n2 n2 = 1 := by
      have h : inner ℝ n2 n2 = ‖n2‖ ^ 2 := real_inner_self_eq_norm_sq n2
      rw [h, hn2] <;> norm_num
    rw [h2, h3, hn_orth] at h1
    have h4 : Real.sin (InnerProductGeometry.angle n1 n2) * (‖n1‖ * ‖n2‖) = 1 := by
      rw [h1] <;> norm_num
    have h5 : ‖n1‖ * ‖n2‖ = 1 := by rw [hn1, hn2] <;> norm_num
    rw [h5] at h4; linarith
  have hv_norm : ‖v‖ = 1 := by
    have h6 : ‖v‖ = ‖n1‖ * ‖n2‖ * Real.sin (InnerProductGeometry.angle n1 n2) :=
      InnerProductGeometry.norm_toLp_symm_crossProduct (n1 : Fin 3 → ℝ) (n2 : Fin 3 → ℝ)
    rw [h6, hn1, hn2, hsin] <;> norm_num
  let f : Fin 3 → Point3 := ![n1, n2, v]
  have hn12 : inner ℝ n1 n2 = 0 := hn_orth
  have hinner_v_n1 : inner ℝ v n1 = 0 := by rw [real_inner_comm n1 v, hinner_n1_v]
  have hinner_v_n2 : inner ℝ v n2 = 0 := by rw [real_inner_comm n2 v, hinner_n2_v]
  have hinner_n2_n1 : inner ℝ n2 n1 = 0 := by rw [real_inner_comm n1 n2, hn12]
  have hfnorm : ∀ (i : Fin 3), ‖f i‖ = 1 := by
    intro i; fin_cases i <;> simp [f, hn1, hn2, hv_norm] <;> norm_num
  have hpair : Pairwise (fun i j : Fin 3 => inner ℝ (f i) (f j) = 0) := by
    intro i j hne
    fin_cases i <;> fin_cases j <;> simp (config := {decide := true}) [f, hn12, hinner_n1_v, hinner_n2_v, hinner_v_n1, hinner_v_n2, hinner_n2_n1] <;> tauto
  have hon : Orthonormal ℝ f := ⟨hfnorm, hpair⟩
  have hli : LinearIndependent ℝ f := hon.linearIndependent
  have hspan : Submodule.span ℝ (Set.range f) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank (by simp)
  let b : OrthonormalBasis (Fin 3) ℝ Point3 :=
    OrthonormalBasis.mk hon hspan.ge
  have hbf : ⇑b = f := OrthonormalBasis.coe_mk hon hspan.ge
  let L : Point3 ≃ₗᵢ[ℝ] Point3 := b.repr
  have hL0 : ∀ (x : Point3), (L x) 0 = inner ℝ x n1 := by
    intro x
    have h : (L x) 0 = inner ℝ (b 0) x := OrthonormalBasis.repr_apply_apply b x 0
    rw [h]
    have h_b0 : b 0 = n1 := by rw [hbf] <;> simp [f]
    rw [h_b0, real_inner_comm]
  have hL1 : ∀ (x : Point3), (L x) 1 = inner ℝ x n2 := by
    intro x
    have h : (L x) 1 = inner ℝ (b 1) x := OrthonormalBasis.repr_apply_apply b x 1
    rw [h]
    have h_b1 : b 1 = n2 := by rw [hbf] <;> simp [f]
    rw [h_b1, real_inner_comm]
  have hL2 : ∀ (x : Point3), (L x) 2 = inner ℝ x v := by
    intro x
    have h : (L x) 2 = inner ℝ (b 2) x := OrthonormalBasis.repr_apply_apply b x 2
    rw [h]
    have h_b2 : b 2 = v := by rw [hbf] <;> simp [f]
    rw [h_b2, real_inner_comm]
  let E : Set Point3 := S1.carrier ∩ S2.carrier
  have h_meas : MeasurableSet E := by
    have h_meas1 : MeasurableSet S1.carrier := by
      have hball : IsClosed (Kakeya.DeltaTube.unitBall) := isClosed_closedBall
      have hthick : IsClosed (Metric.cthickening S1.radius S1.hyperplane) := Metric.isClosed_cthickening
      have h : S1.carrier = Kakeya.DeltaTube.unitBall ∩ Metric.cthickening S1.radius S1.hyperplane := by rfl
      rw [h]; exact (hball.inter hthick).measurableSet
    have h_meas2 : MeasurableSet S2.carrier := by
      have hball : IsClosed (Kakeya.DeltaTube.unitBall) := isClosed_closedBall
      have hthick : IsClosed (Metric.cthickening S2.radius S2.hyperplane) := Metric.isClosed_cthickening
      have h : S2.carrier = Kakeya.DeltaTube.unitBall ∩ Metric.cthickening S2.radius S2.hyperplane := by rfl
      rw [h]; exact (hball.inter hthick).measurableSet
    exact h_meas1.inter h_meas2
  have h_H1_nonempty : S1.hyperplane.Nonempty := by
    have hinner_n : inner ℝ n1 n1 = 1 := by
      have h : inner ℝ n1 n1 = ‖n1‖ ^ 2 := real_inner_self_eq_norm_sq n1
      rw [h, hn1] <;> norm_num
    have h_off : inner ℝ (S1.offset • n1) n1 = S1.offset := by
      have h1 : inner ℝ (S1.offset • n1) n1 = S1.offset * inner ℝ n1 n1 := by simp [inner_smul_left]
      rw [h1, hinner_n] <;> ring
    refine ⟨S1.offset • n1, ?_⟩
    simpa [Kakeya.Slab.hyperplane] using h_off
  have h_H2_nonempty : S2.hyperplane.Nonempty := by
    have hinner_n : inner ℝ n2 n2 = 1 := by
      have h : inner ℝ n2 n2 = ‖n2‖ ^ 2 := real_inner_self_eq_norm_sq n2
      rw [h, hn2] <;> norm_num
    have h_off : inner ℝ (S2.offset • n2) n2 = S2.offset := by
      have h1 : inner ℝ (S2.offset • n2) n2 = S2.offset * inner ℝ n2 n2 := by simp [inner_smul_left]
      rw [h1, hinner_n] <;> ring
    refine ⟨S2.offset • n2, ?_⟩
    simpa [Kakeya.Slab.hyperplane] using h_off
  have h_bound1 : ∀ (z : Point3), z ∈ S1.carrier → |inner ℝ z n1 - S1.offset| ≤ S1.radius := by
    intro z hz
    have h_hyp : S1.hyperplane = {w : Point3 | inner ℝ w n1 = S1.offset} := by ext w; rfl
    have h_ct : Metric.infEDist z S1.hyperplane ≤ ENNReal.ofReal S1.radius := hz.2
    have h9 : ENNReal.ofReal (Metric.infDist z S1.hyperplane) = Metric.infEDist z S1.hyperplane := by
      rw [← ENNReal.ofReal_toReal (Metric.infEDist_ne_top h_H1_nonempty)] <;> rfl
    have h_dist : Metric.infDist z S1.hyperplane ≤ S1.radius := by
      rw [← h9] at h_ct
      exact (ENNReal.ofReal_le_ofReal_iff S1.radius_nonneg).mp h_ct
    rw [h_hyp] at h_dist
    have h_eq : Metric.infDist z {w : Point3 | inner ℝ w n1 = S1.offset} = |inner ℝ z n1 - S1.offset| :=
      dist_to_hyperplane (n := n1) (offset := S1.offset) (x := z) hn1
    rw [h_eq] at h_dist
    exact h_dist
  have h_bound2 : ∀ (z : Point3), z ∈ S2.carrier → |inner ℝ z n2 - S2.offset| ≤ S2.radius := by
    intro z hz
    have h_hyp : S2.hyperplane = {w : Point3 | inner ℝ w n2 = S2.offset} := by ext w; rfl
    have h_ct : Metric.infEDist z S2.hyperplane ≤ ENNReal.ofReal S2.radius := hz.2
    have h9 : ENNReal.ofReal (Metric.infDist z S2.hyperplane) = Metric.infEDist z S2.hyperplane := by
      rw [← ENNReal.ofReal_toReal (Metric.infEDist_ne_top h_H2_nonempty)] <;> rfl
    have h_dist : Metric.infDist z S2.hyperplane ≤ S2.radius := by
      rw [← h9] at h_ct
      exact (ENNReal.ofReal_le_ofReal_iff S2.radius_nonneg).mp h_ct
    rw [h_hyp] at h_dist
    have h_eq : Metric.infDist z {w : Point3 | inner ℝ w n2 = S2.offset} = |inner ℝ z n2 - S2.offset| :=
      dist_to_hyperplane (n := n2) (offset := S2.offset) (x := z) hn2
    rw [h_eq] at h_dist
    exact h_dist
  have h_bound3 : ∀ (z : Point3), z ∈ Kakeya.DeltaTube.unitBall → |inner ℝ z v| ≤ 1 := by
    intro z hz
    have hzn : ‖z‖ ≤ 1 := by simpa [Kakeya.DeltaTube.unitBall, Metric.mem_closedBall] using hz
    have h : |inner ℝ z v| ≤ ‖z‖ * ‖v‖ := abs_real_inner_le_norm z v
    have hv_norm : ‖v‖ = 1 := by
      have h6 : ‖v‖ = ‖n1‖ * ‖n2‖ * Real.sin (InnerProductGeometry.angle n1 n2) :=
        InnerProductGeometry.norm_toLp_symm_crossProduct (n1 : Fin 3 → ℝ) (n2 : Fin 3 → ℝ)
      rw [h6, hn1, hn2, hsin] <;> norm_num
    rw [hv_norm] at h
    linarith
  have h_d0 : ∀ (x y : Point3), x ∈ E → y ∈ E → |(L x) 0 - (L y) 0| ≤ 2 * S1.radius := by
    intro x y hx hy
    rw [hL0, hL0]
    have hx1 : |inner ℝ x n1 - S1.offset| ≤ S1.radius := h_bound1 x hx.1
    have hy1 : |inner ℝ y n1 - S1.offset| ≤ S1.radius := h_bound1 y hy.1
    calc |inner ℝ x n1 - inner ℝ y n1|
      = |(inner ℝ x n1 - S1.offset) - (inner ℝ y n1 - S1.offset)| := by ring_nf
    _ ≤ |inner ℝ x n1 - S1.offset| + |inner ℝ y n1 - S1.offset| := by exact abs_sub _ _
    _ ≤ S1.radius + S1.radius := by linarith
    _ = 2 * S1.radius := by ring
  have h_d1 : ∀ (x y : Point3), x ∈ E → y ∈ E → |(L x) 1 - (L y) 1| ≤ 2 * S2.radius := by
    intro x y hx hy
    rw [hL1, hL1]
    have hx2 : |inner ℝ x n2 - S2.offset| ≤ S2.radius := h_bound2 x hx.2
    have hy2 : |inner ℝ y n2 - S2.offset| ≤ S2.radius := h_bound2 y hy.2
    calc |inner ℝ x n2 - inner ℝ y n2|
      = |(inner ℝ x n2 - S2.offset) - (inner ℝ y n2 - S2.offset)| := by ring_nf
    _ ≤ |inner ℝ x n2 - S2.offset| + |inner ℝ y n2 - S2.offset| := by exact abs_sub _ _
    _ ≤ S2.radius + S2.radius := by linarith
    _ = 2 * S2.radius := by ring
  have h_d2 : ∀ (x y : Point3), x ∈ E → y ∈ E → |(L x) 2 - (L y) 2| ≤ 2 := by
    intro x y hx hy
    rw [hL2, hL2]
    have hx_ball : x ∈ Kakeya.DeltaTube.unitBall := hx.1.1
    have hy_ball : y ∈ Kakeya.DeltaTube.unitBall := hy.1.1
    have hx3 : |inner ℝ x v| ≤ 1 := h_bound3 x hx_ball
    have hy3 : |inner ℝ y v| ≤ 1 := h_bound3 y hy_ball
    calc |inner ℝ x v - inner ℝ y v|
      ≤ |inner ℝ x v| + |inner ℝ y v| := by exact abs_sub _ _
    _ ≤ 1 + 1 := by linarith
    _ = 2 := by norm_num
  have h_main : volume E ≤ ENNReal.ofReal ((2 * S1.radius) * (2 * S2.radius) * (2 : ℝ)) :=
    Kakeya.Hairbrush.volume_diameter_bound h_meas L (2 * S1.radius) (2 * S2.radius) 2
      (by linarith [S1.radius_nonneg]) (by linarith [S2.radius_nonneg]) (by norm_num) h_d0 h_d1 h_d2
  have h_final : (2 * S1.radius) * (2 * S2.radius) * (2 : ℝ) ≤ 1000000 * capRadius ^ 2 := by
    have h1 : (2 * S1.radius) * (2 * S2.radius) * (2 : ℝ) = 8 * S1.radius * S2.radius := by ring
    rw [h1]
    have h4 : 0 ≤ S1.radius := S1.radius_nonneg
    have h5 : 0 ≤ S2.radius := S2.radius_nonneg
    nlinarith [hr1, hr2, sq_nonneg (capRadius)]
  exact h_main.trans (ENNReal.ofReal_le_ofReal h_final)

end Kakeya.Assouad

import MyLeanRepo.Kakeya.Assouad.Subunit.HairbrushStatements
import MyLeanRepo.Kakeya.Assouad.HairbrushBalancedBroadDecomposition.SlabContainment
import MyLeanRepo.Kakeya.Assouad.HairbrushBalancedBroadDecomposition.SlabVolumeBound
import MyLeanRepo.Kakeya.Assouad.HairbrushBalancedBroadDecomposition.SlabGeometryHelpers
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Int.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic

/-!
# Helper lemmas for slab incidence grouping

Provides:
1. Bounds on strip indices for points in the unit ball.
2. Finite enumeration of nonempty (direction-label, strip-index) pairs.
3. Mass additivity for a measurable partition of a shading.
-/

noncomputable section

open MeasureTheory Metric Set Finset Real

attribute [local instance] Classical.propDecidable

namespace Kakeya.Assouad

/-- If x is in the unit ball and n is a unit vector, then |inner ℝ x n| ≤ 1. -/
lemma inner_unit_ball_bound {x n : Point3} (hx : x ∈ Kakeya.DeltaTube.unitBall)
    (hn : ‖n‖ = 1) : |inner ℝ x n| ≤ 1 := by
  have h1 : ‖x‖ ≤ 1 := by
    simpa [Kakeya.DeltaTube.unitBall, Metric.mem_closedBall, dist_eq_norm] using hx
  have h2 : |inner ℝ x n| ≤ ‖x‖ * ‖n‖ := abs_real_inner_le_norm x n
  rw [hn] at h2
  linarith

/-- The strip index floor(inner x n / capRadius) lies in a finite interval. -/
lemma strip_index_in_range {x n : Point3} (hx : x ∈ Kakeya.DeltaTube.unitBall)
    (hn : ‖n‖ = 1) {capRadius : ℝ} (hcap_pos : 0 < capRadius) :
    Int.floor (inner ℝ x n / capRadius) ∈
      Finset.Icc (-(Int.ceil (1 / capRadius))) (Int.ceil (1 / capRadius)) := by
  have h1 : |inner ℝ x n| ≤ 1 := inner_unit_ball_bound hx hn
  have h2 : -1 ≤ inner ℝ x n := by linarith [abs_le.mp h1]
  have h3 : inner ℝ x n ≤ 1 := by linarith [abs_le.mp h1]
  have h4 : -(1 / capRadius) ≤ inner ℝ x n / capRadius := by
    have h41 : (-1 : ℝ) / capRadius ≤ inner ℝ x n / capRadius := by
      apply div_le_div_of_nonneg_right h2 (by linarith)
    have h42 : (-(1 / capRadius) : ℝ) = (-1 : ℝ) / capRadius := by ring
    rw [h42]
    exact h41
  have h5 : inner ℝ x n / capRadius ≤ 1 / capRadius := by
    apply div_le_div_of_nonneg_right h3 (by linarith)
  have h6 : Int.floor (-(1 / capRadius)) ≤ Int.floor (inner ℝ x n / capRadius) :=
    Int.floor_mono h4
  have h7 : Int.floor (inner ℝ x n / capRadius) ≤ Int.floor (1 / capRadius) :=
    Int.floor_mono h5
  have h8 : Int.floor (-(1 / capRadius)) = -Int.ceil (1 / capRadius) := by
    simpa using Int.floor_neg
  rw [h8] at h6
  have h9 : Int.floor (1 / capRadius) ≤ Int.ceil (1 / capRadius) :=
    Int.floor_le_ceil (1 / capRadius)
  exact Finset.mem_Icc.mpr ⟨h6, le_trans h7 h9⟩

/-- A shading with nonzero mass has a nonempty union. -/
lemma shading_mass_nonzero_implies_union_nonempty {δ : ℝ} {F : Kakeya.TubeFamily δ}
    {Y : Kakeya.Shading F} (h_mass : Y.mass ≠ 0) : Y.union.Nonempty := by
  have h1 : ∃ T ∈ F, MeasureTheory.volume (Y.carrier T) ≠ 0 := by
    by_contra h
    push Not at h
    have h2 : ∀ T ∈ F, MeasureTheory.volume (Y.carrier T) = 0 := by
      intro T hT
      exact h T hT
    have h3 : Y.mass = 0 := by
      dsimp only [Kakeya.Shading.mass]
      rw [Finset.sum_congr rfl (fun T _ => h2 T ‹_›)]
      simp
    exact h_mass h3
  rcases h1 with ⟨T, hT, hvol⟩
  have h4 : (Y.carrier T).Nonempty := by
    by_contra h5
    have h6 : Y.carrier T = ∅ := Set.not_nonempty_iff_eq_empty.mp h5
    rw [h6] at hvol
    simp at hvol
  rcases h4 with ⟨x, hx⟩
  exact ⟨x, Set.mem_setOf.mpr ⟨T, hT, hx⟩⟩

/-- Construct the finite set of all candidate (label, strip) pairs. -/
def allStripPairs {labelCount : ℕ} (capRadius : ℝ) :
    Finset (Fin labelCount × ℤ) :=
  Finset.biUnion (Finset.univ : Finset (Fin labelCount)) fun j =>
    (Finset.Icc (-(Int.ceil (1 / capRadius))) (Int.ceil (1 / capRadius))).image
      (fun k : ℤ => (j, k))

/-- A point x with label j and strip index k is a witness that pair (j,k) is nonempty. -/
lemma point_witnesses_pair {labelCount : ℕ} {capRadius : ℝ} (hcap_pos : 0 < capRadius)
    (normal : Fin labelCount → Point3) (hnormal : ∀ j, ‖normal j‖ = 1)
    (label : Point3 → Fin labelCount) (S : Set Point3)
    (x : Point3) (_hxS : x ∈ S) (hx_ball : x ∈ Kakeya.DeltaTube.unitBall)
    (j : Fin labelCount) (_hj : label x = j) :
    (j, Int.floor (inner ℝ x (normal j) / capRadius)) ∈ allStripPairs capRadius := by
  have h_k_in : Int.floor (inner ℝ x (normal j) / capRadius) ∈
      Finset.Icc (-(Int.ceil (1 / capRadius))) (Int.ceil (1 / capRadius)) :=
    strip_index_in_range hx_ball (hnormal j) hcap_pos
  simp only [allStripPairs, Finset.mem_biUnion, Finset.mem_univ, true_and]
  refine ⟨j, ?_⟩
  exact Finset.mem_image.mpr ⟨_, h_k_in, rfl⟩

/-- Filter to only nonempty pairs. -/
def nonemptyStripPairs {labelCount : ℕ} {capRadius : ℝ}
    (normal : Fin labelCount → Point3)
    (label : Point3 → Fin labelCount)
    (S : Set Point3) : Finset (Fin labelCount × ℤ) :=
  (allStripPairs capRadius).filter fun p =>
    (S ∩ {x | label x = p.1 ∧
      Int.floor (inner ℝ x (normal p.1) / capRadius) = p.2}).Nonempty

/-- If S is nonempty and contained in the unit ball, then nonemptyStripPairs is nonempty. -/
lemma nonemptyStripPairs_nonempty {labelCount : ℕ} {capRadius : ℝ}
    (hcap_pos : 0 < capRadius)
    (normal : Fin labelCount → Point3) (hnormal : ∀ j, ‖normal j‖ = 1)
    (label : Point3 → Fin labelCount)
    (S : Set Point3) (hS_sub_ball : S ⊆ Kakeya.DeltaTube.unitBall)
    (hS_nonempty : S.Nonempty) :
    (nonemptyStripPairs (capRadius := capRadius) normal label S).Nonempty := by
  rcases hS_nonempty with ⟨x, hxS⟩
  let j := label x
  let k := Int.floor (inner ℝ x (normal j) / capRadius)
  have hx_ball : x ∈ Kakeya.DeltaTube.unitBall := hS_sub_ball hxS
  have h_pair_in_all : (j, k) ∈ allStripPairs capRadius :=
    point_witnesses_pair hcap_pos normal hnormal label S x hxS hx_ball j rfl
  have h_witness : x ∈ S ∩ {x : Point3 | label x = j ∧
      Int.floor (inner ℝ x (normal j) / capRadius) = k} := by
    exact ⟨hxS, by simp [j, k]⟩
  have h_nonempty : (S ∩ {x : Point3 | label x = j ∧
      Int.floor (inner ℝ x (normal j) / capRadius) = k}).Nonempty :=
    ⟨x, h_witness⟩
  have h_in_filter : (j, k) ∈ nonemptyStripPairs (capRadius := capRadius) normal label S := by
    rw [nonemptyStripPairs, Finset.mem_filter]
    exact ⟨h_pair_in_all, h_nonempty⟩
  exact ⟨(j, k), h_in_filter⟩

/-- Equivalence between Fin card and the elements of a finset. -/
def finsetEquiv {α : Type*} [DecidableEq α] (s : Finset α) (_hs : s.Nonempty) :
    Fin s.card ≃ {x : α // x ∈ s} :=
  (Finset.equivFin s).symm

/-!
## Mass additivity for a measurable partition

Given a shading Y and a finite measurable partition of its union,
the total mass is the sum of the restricted masses.
-/

/-- Incidence mass additivity over a measurable partition.

Let `assignSet j` be a finite pairwise-disjoint family of measurable sets
covering `Y.union`. For each group `j`, let `family j ⊆ F` and define
`shading j .carrier T := Y.carrier T ∩ assignSet j` for all `T ∈ F`.

Assume that for `T ∉ family j`, the intersection `Y.carrier T ∩ assignSet j`
is empty (so the tube does not belong to that group).

Then `∑ j, (shading j).mass = Y.mass`.
-/
lemma incidence_mass_additivity
    {δ : ℝ} {N : ℕ} {F : Kakeya.TubeFamily δ}
    (Y : Kakeya.Shading F)
    (assignSet : Fin N → Set Point3)
    (hassign_meas : ∀ j, MeasurableSet (assignSet j))
    (hassign_disj : ∀ j k, j ≠ k → Disjoint (assignSet j) (assignSet k))
    (hassign_cover : Y.union ⊆ ⋃ j, assignSet j)
    (family : Fin N → Kakeya.TubeFamily δ)
    (hfamily_sub : ∀ j, family j ⊆ F)
    (shading : ∀ j, Kakeya.Shading (family j))
    (hshading_eq : ∀ j T, T ∈ F →
      (shading j).carrier T = Y.carrier T ∩ assignSet j)
    (hzero : ∀ j T, T ∈ F → T ∉ family j →
      Y.carrier T ∩ assignSet j = ∅) :
    ∑ j : Fin N, (shading j).mass = Y.mass := by
  -- For each j, extend the mass sum from family j to all of F by adding zeros
  have h1 : ∀ j : Fin N, (shading j).mass =
      ∑ T ∈ F, MeasureTheory.volume ((shading j).carrier T) := by
    intro j
    dsimp only [Kakeya.Shading.mass]
    apply Finset.sum_subset (hfamily_sub j)
    intro T hT _
    have hT_notin : T ∉ family j := by tauto
    have h_empty1 : Y.carrier T ∩ assignSet j = ∅ := hzero j T hT hT_notin
    have h_empty2 : (shading j).carrier T = ∅ := by
      rw [hshading_eq j T hT, h_empty1]
    rw [h_empty2]
    simp
  have h_main : ∑ j : Fin N, (shading j).mass =
      ∑ T ∈ F, ∑ j : Fin N, MeasureTheory.volume ((shading j).carrier T) := by
    have h_sum1 : ∑ j : Fin N, (shading j).mass =
        ∑ j : Fin N, ∑ T ∈ F, MeasureTheory.volume ((shading j).carrier T) := by
      apply Finset.sum_congr rfl
      intro j _
      exact h1 j
    rw [h_sum1, Finset.sum_comm]
  rw [h_main]
  apply Finset.sum_congr rfl
  intro T hT
  -- For each T, the sets (shading j).carrier T partition Y.carrier T
  have h2 : ∀ j : Fin N, MeasurableSet ((shading j).carrier T) := by
    intro j
    rw [hshading_eq j T hT]
    exact (Y.measurable_carrier hT).inter (hassign_meas j)
  have h3 : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin N)))
      (fun j : Fin N => (shading j).carrier T) := by
    intro j _ k _ hne
    have h_eqj : (shading j).carrier T = Y.carrier T ∩ assignSet j := hshading_eq j T hT
    have h_eqk : (shading k).carrier T = Y.carrier T ∩ assignSet k := hshading_eq k T hT
    dsimp only [Function.onFun]
    rw [h_eqj, h_eqk]
    exact Disjoint.mono (Set.inter_subset_right) (Set.inter_subset_right)
      (hassign_disj j k hne)
  have h4 : (⋃ j : Fin N, (shading j).carrier T) = Y.carrier T := by
    apply Set.Subset.antisymm
    · intro x hx
      rcases Set.mem_iUnion.mp hx with ⟨j, hxj⟩
      rw [hshading_eq j T hT] at hxj
      exact hxj.1
    · intro x hx
      have hxY : x ∈ Y.union := Set.mem_setOf.mpr ⟨T, hT, hx⟩
      have h5 : x ∈ ⋃ j, assignSet j := hassign_cover hxY
      rcases Set.mem_iUnion.mp h5 with ⟨j, hxj⟩
      have h6 : x ∈ Y.carrier T ∩ assignSet j := ⟨hx, hxj⟩
      have h7 : T ∈ family j := by
        by_contra h8
        have h9 : Y.carrier T ∩ assignSet j = ∅ := hzero j T hT h8
        rw [h9] at h6
        simp at h6
      have h10 : x ∈ (shading j).carrier T := by
        rw [hshading_eq j T hT]
        exact h6
      exact Set.mem_iUnion.mpr ⟨j, h10⟩
  have h5 : MeasureTheory.volume (Y.carrier T) =
      ∑ j : Fin N, MeasureTheory.volume ((shading j).carrier T) := by
    have h_univ_eq : (⋃ j : Fin N, (shading j).carrier T) =
        (⋃ j ∈ (Finset.univ : Finset (Fin N)), (shading j).carrier T) := by
      ext x
      simp [Set.mem_iUnion]
    have h6 : MeasureTheory.volume (⋃ j ∈ (Finset.univ : Finset (Fin N)), (shading j).carrier T) =
        ∑ j : Fin N, MeasureTheory.volume ((shading j).carrier T) := by
      rw [MeasureTheory.measure_biUnion_finset h3 (fun b _ => h2 b)]
    rw [h_univ_eq] at h4
    rw [← h6, h4]
  exact h5.symm

/-!
## Group angular confinement and slab containment
-/

/-- A group filtered by direction label is angularly confined to capRadius. -/
lemma group_angular_confinement
    {δ capRadius : ℝ}
    {F : Kakeya.TubeFamily δ}
    {Y : Kakeya.Shading F}
    {labelCount : ℕ}
    {label : Point3 → Fin labelCount}
    {center : Fin labelCount → Point3}
    (hcenter_unit : ∀ j, ‖center j‖ = 1)
    (h_pointwise : ∀ x ∈ Y.union, ∀ T ∈ F, x ∈ Y.carrier T →
        hairbrushAcuteDirectionAngle T.direction (center (label x)) ≤ capRadius)
    (j : Fin labelCount)
    (family_j : Kakeya.TubeFamily δ)
    (h_family_has_label : ∀ T ∈ family_j, T ∈ F ∧ ∃ x ∈ Y.carrier T, label x = j) :
    HairbrushAngularlyConfined family_j capRadius := by
  refine ⟨center j, hcenter_unit j, ?_⟩
  intro T hT
  have h1 : T ∈ F ∧ ∃ x ∈ Y.carrier T, label x = j := h_family_has_label T hT
  rcases h1 with ⟨hT_F, x, hxT, hxj⟩
  have hx_union : x ∈ Y.union := Set.mem_setOf.mpr ⟨T, hT_F, hxT⟩
  have h2 : hairbrushAcuteDirectionAngle T.direction (center (label x)) ≤ capRadius :=
    h_pointwise x hx_union T hT_F hxT
  rw [hxj] at h2
  exact h2

/-- A group filtered by direction label and strip index is contained in one slab.

The slab has normal `n j`, offset at the center of strip `k`, and radius
`4 * capRadius`. Its volume is at most `32 * capRadius ≤ 100 * capRadius`.
-/
lemma group_slab_containment
    {δ capRadius : ℝ} (hδ : 0 < δ) (hcap : δ ≤ capRadius) (hcap1 : capRadius ≤ 1)
    {F : Kakeya.TubeFamily δ}
    {Y : Kakeya.Shading F}
    {labelCount : ℕ}
    {label : Point3 → Fin labelCount}
    {center : Fin labelCount → Point3}
    (hcenter_unit : ∀ j, ‖center j‖ = 1)
    (n : Fin labelCount → Point3)
    (hn_unit : ∀ j, ‖n j‖ = 1)
    (hn_orth : ∀ j, inner ℝ (center j) (n j) = 0)
    (h_pointwise : ∀ x ∈ Y.union, ∀ T ∈ F, x ∈ Y.carrier T →
        hairbrushAcuteDirectionAngle T.direction (center (label x)) ≤ capRadius)
    (hF_unit : F.IsInUnitBall)
    (j : Fin labelCount) (k : ℤ)
    (family_jk : Kakeya.TubeFamily δ)
    (h_family_def : family_jk = F.filter (fun T =>
        ∃ x ∈ Y.carrier T, label x = j ∧
          Int.floor (inner ℝ x (n j) / capRadius) = k)) :
    ∃ (S : Kakeya.Slab),
        (∀ T ∈ family_jk, T.carrier ⊆ S.carrier) ∧
        volume S.carrier ≤ ENNReal.ofReal (100 * capRadius) := by
  have hcap_pos : 0 < capRadius := by linarith
  let offset : ℝ := (k : ℝ) * capRadius + capRadius / 2
  let radius : ℝ := 4 * capRadius
  have hradius_nonneg : 0 ≤ radius := by
    dsimp only [radius]
    <;> linarith
  let S : Kakeya.Slab :=
    { normal := n j
      offset := offset
      radius := radius
      normal_unit := hn_unit j
      radius_nonneg := hradius_nonneg }
  have h_main : ∀ T ∈ family_jk, T.carrier ⊆ S.carrier := by
    intro T hT y hy
    have hT_F : T ∈ F := by
      rw [h_family_def] at hT
      exact (Finset.mem_filter.mp hT).1
    have h1 : ∃ x ∈ Y.carrier T, label x = j ∧
        Int.floor (inner ℝ x (n j) / capRadius) = k := by
      rw [h_family_def] at hT
      exact (Finset.mem_filter.mp hT).2
    rcases h1 with ⟨x, hxT, hxj, hxk⟩
    have hx_union : x ∈ Y.union := Set.mem_setOf.mpr ⟨T, hT_F, hxT⟩
    have hx_carrier : x ∈ T.carrier := Y.subset_tube hT_F hxT
    have hx_ball : x ∈ Kakeya.DeltaTube.unitBall := hF_unit hT_F hx_carrier
    have hy_ball : y ∈ Kakeya.DeltaTube.unitBall := hF_unit hT_F hy
    have h_angle : hairbrushAcuteDirectionAngle T.direction (center j) ≤ capRadius := by
      have h2 := h_pointwise x hx_union T hT_F hxT
      rw [hxj] at h2
      exact h2
    have h_strip1 : (k : ℝ) ≤ inner ℝ x (n j) / capRadius :=
      Int.le_floor.mp (le_of_eq hxk.symm)
    have h_strip2 : inner ℝ x (n j) / capRadius < (k : ℝ) + 1 := by
      have h := Int.lt_floor_add_one (inner ℝ x (n j) / capRadius)
      rw [hxk] at h
      exact h
    have h51 : (k : ℝ) * capRadius ≤ inner ℝ x (n j) := by
      have h : (k : ℝ) * capRadius ≤ (inner ℝ x (n j) / capRadius) * capRadius := by
        gcongr
      have h2 : (inner ℝ x (n j) / capRadius) * capRadius = inner ℝ x (n j) := by
        field_simp [hcap_pos.ne'] <;> ring
      rw [h2] at h
      exact h
    have h52 : inner ℝ x (n j) < ((k : ℝ) + 1) * capRadius := by
      have h : (inner ℝ x (n j) / capRadius) * capRadius < ((k : ℝ) + 1) * capRadius := by
        gcongr
      have h2 : (inner ℝ x (n j) / capRadius) * capRadius = inner ℝ x (n j) := by
        field_simp [hcap_pos.ne'] <;> ring
      rw [h2] at h
      exact h
    have h4 : |inner ℝ x (n j) - offset| ≤ capRadius / 2 := by
      have h13 : inner ℝ x (n j) - offset ≤ capRadius / 2 := by
        dsimp only [offset]
        linarith
      have h14 : -(capRadius / 2) ≤ inner ℝ x (n j) - offset := by
        dsimp only [offset]
        linarith
      exact abs_le.mpr ⟨h14, h13⟩
    have h_var : |inner ℝ x (n j) - inner ℝ y (n j)| ≤ 2 * δ + capRadius := by
      have h := tube_projection_variation hδ hcap hcap1 T (center j) (n j)
        (hcenter_unit j) (hn_unit j) (hn_orth j) h_angle x y hx_carrier hy
      linarith
    have h_var' : |inner ℝ y (n j) - inner ℝ x (n j)| ≤ 2 * δ + capRadius := by
      have h_comm : |inner ℝ y (n j) - inner ℝ x (n j)| =
          |inner ℝ x (n j) - inner ℝ y (n j)| := abs_sub_comm _ _
      rw [h_comm]
      exact h_var
    have h5 : |inner ℝ y (n j) - offset| ≤ radius := by
      calc
        |inner ℝ y (n j) - offset|
          = |(inner ℝ y (n j) - inner ℝ x (n j)) + (inner ℝ x (n j) - offset)| := by ring_nf
        _ ≤ |inner ℝ y (n j) - inner ℝ x (n j)| + |inner ℝ x (n j) - offset| := abs_add_le _ _
        _ ≤ (2 * δ + capRadius) + capRadius / 2 := by gcongr
        _ ≤ radius := by
          dsimp only [radius]
          linarith
    have h_H_nonempty : S.hyperplane.Nonempty := by
      have hinner_n : inner ℝ (n j) (n j) = (1 : ℝ) := by
        have h : inner ℝ (n j) (n j) = ‖n j‖ ^ 2 := real_inner_self_eq_norm_sq (n j)
        rw [h, hn_unit j] <;> norm_num
      have h_off : inner ℝ (offset • (n j)) (n j) = offset := by
        have h1 : inner ℝ (offset • (n j)) (n j) = offset * inner ℝ (n j) (n j) := by
          simp [inner_smul_left]
        rw [h1, hinner_n] <;> ring
      refine ⟨offset • (n j), ?_⟩
      simpa [S, Kakeya.Slab.hyperplane] using h_off
    have h_dist_eq : Metric.infDist y S.hyperplane = |inner ℝ y (n j) - offset| := by
      have h_hyperplane : S.hyperplane = {z : Point3 | inner ℝ z (n j) = offset} := by
        ext z
        simp [S, Kakeya.Slab.hyperplane] <;> rfl
      rw [h_hyperplane]
      exact dist_to_hyperplane (hn_unit j)
    have h_cthick : y ∈ Metric.cthickening S.radius S.hyperplane := by
      have h6 : Metric.infDist y S.hyperplane ≤ S.radius := by
        rw [h_dist_eq]
        exact h5
      have h7 : ENNReal.ofReal (Metric.infDist y S.hyperplane) = Metric.infEDist y S.hyperplane := by
        rw [← ENNReal.ofReal_toReal (Metric.infEDist_ne_top h_H_nonempty)] <;> rfl
      have h8 : Metric.infEDist y S.hyperplane ≤ ENNReal.ofReal S.radius := by
        rw [← h7]
        exact ENNReal.ofReal_le_ofReal h6
      exact h8
    exact ⟨hy_ball, h_cthick⟩
  have h_vol : volume S.carrier ≤ ENNReal.ofReal (100 * capRadius) := by
    have h9 : volume S.carrier ≤ ENNReal.ofReal (8 * S.radius) := slab_volume_le S
    have h10 : S.radius = radius := by rfl
    rw [h10] at h9
    have h11 : (8 * radius : ℝ) ≤ 100 * capRadius := by
      dsimp only [radius]
      <;> linarith
    exact h9.trans (ENNReal.ofReal_le_ofReal h11)
  exact ⟨S, h_main, h_vol⟩

/-!
## Union partition

Group unions are pairwise disjoint and their union equals the original shading union.
-/

/-- Group unions form a partition of the original shading union.

If each point is assigned a unique label `pointLabel x`, and groups correspond
to distinct labels, then the group unions are pairwise disjoint and their
union is exactly `Y.union`.
-/
lemma group_union_partition
    {δ : ℝ} {F : Kakeya.TubeFamily δ} {Y : Kakeya.Shading F}
    {labelCount : ℕ} {label : Point3 → Fin labelCount}
    (n : Fin labelCount → Point3) (capRadius : ℝ) (hcap : 0 < capRadius)
    (groups : Finset (Fin labelCount × ℤ))
    (pointLabel : Point3 → Fin labelCount × ℤ)
    (hpointLabel_def : ∀ x, pointLabel x = (label x, Int.floor (inner ℝ x (n (label x)) / capRadius)))
    (h_groups_valid : ∀ p ∈ groups, ∃ x ∈ Y.union, pointLabel x = p)
    (h_groups_complete : ∀ x ∈ Y.union, pointLabel x ∈ groups)
    (family : (Fin labelCount × ℤ) → Kakeya.TubeFamily δ)
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
    have h_ex : ∃ (p : Fin labelCount × ℤ), p ∈ groups ∧ x ∈ (shading p).union := by
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

end Kakeya.Assouad

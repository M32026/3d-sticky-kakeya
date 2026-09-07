import MyLeanRepo.Kakeya.Assouad.Subunit.HairbrushSelfContainedLeaves
import MyLeanRepo.Kakeya.Assouad.HairbrushBalancedBroadDecomposition.DirectionPacking2D
import MyLeanRepo.Kakeya.Assouad.HairbrushBalancedBroadDecomposition.SlabGroupingHelpers
import MyLeanRepo.Kakeya.Assouad.HairbrushBalancedBroadDecomposition.TripleLabelGroupingHelpers
import MyLeanRepo.Kakeya.Streamlined.VolumeHelpers
import MyLeanRepo.Kakeya.Hairbrush.IntersectionSumBound.Preparations
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Coarse-tube incidence grouping (Wang–Zahl B.32–B.33)

This module proves `hairbrush_coarse_tube_incidence_grouping`.  It uses two
transverse strip labels per direction (triple index) and produces convex
quadratic-volume containers while preserving the grouping API consumed
downstream.

## Main steps

1. Extend each angular center to an orthonormal frame `(v, n1, n2)`.
2. Label each retained point by `(j, floor(<x,n1>/capRadius), floor(<x,n2>/capRadius))`.
3. Enumerate nonempty labels and build a filtered family + shading per group.
4. Prove nonempty, family subset, exact disjoint union, incidence-mass additivity,
   label consistency, angular confinement, and two-broadness transfer.
5. Place every full tube in the intersection of two transverse slabs and the unit ball.
6. Bound the container volume by `1000000 * capRadius^2` via a measure-preserving
   orthonormal coordinate map and `volume_diameter_bound`.
7. Bound each tube's occurrence across groups by `1000000`.

## Key dependencies

* `TripleLabelGroupingHelpers` — `exists_orthonormal_frame`, `tube_occurrence_bound_triple`,
  `nonemptyTripleLabels`, and related enumeration lemmas.
* `SlabGroupingHelpers` — slab containment, two-broadness transfer, mass additivity.
* `Kakeya.Hairbrush.volume_diameter_bound` — diameter-based volume estimate.
-/

noncomputable section

open MeasureTheory Metric Set Finset Real

attribute [local instance] Classical.propDecidable

namespace Kakeya.Assouad

/-! ## Helper lemmas -/

/-- Volume of intersection of two slabs with transverse normals and unit ball. -/
lemma two_slab_container_volume
    {capRadius : ℝ} (hcap_pos : 0 < capRadius)
    (v n1 n2 : Point3)
    (hv : ‖v‖ = 1) (hn1 : ‖n1‖ = 1) (hn2 : ‖n2‖ = 1)
    (h_orth1 : inner ℝ v n1 = 0) (h_orth2 : inner ℝ v n2 = 0)
    (h_orth12 : inner ℝ n1 n2 = 0)
    (S1 S2 : Kakeya.Slab)
    (hS1_normal : S1.normal = n1) (hS2_normal : S2.normal = n2)
    (hS1_radius : S1.radius ≤ 4 * capRadius)
    (hS2_radius : S2.radius ≤ 4 * capRadius) :
    volume (S1.carrier ∩ S2.carrier) ≤
      ENNReal.ofReal (1000000 * capRadius ^ 2) := by
  let vec : Fin 3 → Point3 := ![v, n1, n2]
  have hcomm : ∀ (a b : Point3), inner ℝ a b = inner ℝ b a := by
    intro a b
    exact (real_inner_comm a b).symm
  have h_orth1' : inner ℝ n1 v = 0 := by rw [hcomm]; exact h_orth1
  have h_orth2' : inner ℝ n2 v = 0 := by rw [hcomm]; exact h_orth2
  have h_orth12' : inner ℝ n2 n1 = 0 := by rw [hcomm]; exact h_orth12
  have h1vec : ∀ (i : Fin 3), ‖vec i‖ = 1 := by
    intro i
    fin_cases i <;> simp [vec, hv, hn1, hn2]
  have h2vec : Pairwise (fun (i j : Fin 3) => inner ℝ (vec i) (vec j) = 0) := by
    intro i j hne
    fin_cases i <;> fin_cases j <;> simp (config := {decide := true}) [vec, h_orth1, h_orth1', h_orth2, h_orth2', h_orth12, h_orth12'] <;> tauto
  have h_orthonormal : Orthonormal ℝ vec := ⟨h1vec, h2vec⟩
  have h_card : Fintype.card (Fin 3) = Module.finrank ℝ Point3 := by
    have h : Module.finrank ℝ Point3 = Fintype.card (Fin 3) := finrank_euclideanSpace
    exact h.symm
  let basis := basisOfOrthonormalOfCardEqFinrank h_orthonormal h_card
  have h_coe_basis : ⇑basis = vec := coe_basisOfOrthonormalOfCardEqFinrank h_orthonormal h_card
  have h_orthonormal' : Orthonormal ℝ ⇑basis := by
    rw [h_coe_basis] <;> exact h_orthonormal
  let b : OrthonormalBasis (Fin 3) ℝ Point3 :=
    basis.toOrthonormalBasis h_orthonormal'
  have h_coe_b : (b : Fin 3 → Point3) = (basis : Fin 3 → Point3) :=
    Module.Basis.coe_toOrthonormalBasis basis h_orthonormal'
  have h_b0 : b 0 = v := by
    have h1 : b 0 = basis 0 := congrFun h_coe_b 0
    have h2 : basis 0 = v := by rw [h_coe_basis] <;> rfl
    exact Eq.trans h1 h2
  have h_b1 : b 1 = n1 := by
    have h1 : b 1 = basis 1 := congrFun h_coe_b 1
    have h2 : basis 1 = n1 := by rw [h_coe_basis] <;> rfl
    exact Eq.trans h1 h2
  have h_b2 : b 2 = n2 := by
    have h1 : b 2 = basis 2 := congrFun h_coe_b 2
    have h2 : basis 2 = n2 := by rw [h_coe_basis] <;> rfl
    exact Eq.trans h1 h2
  let b' : OrthonormalBasis (Fin 3) ℝ Point3 := EuclideanSpace.basisFun (Fin 3) ℝ
  let A : Point3 ≃ₗᵢ[ℝ] Point3 := b.equiv b' (Equiv.refl (Fin 3))
  have h_coord : ∀ (x : Point3) (i : Fin 3), (A x) i = inner ℝ x (b i) := by
    intro x i
    have h1 : (A x) i = b'.repr (A x) i := by rw [EuclideanSpace.basisFun_repr]
    rw [h1]
    have h2 : b'.repr (A x) = b.repr x := by rfl
    rw [h2, b.repr_apply_apply]
    <;> rw [hcomm]
  let E : Set Point3 := S1.carrier ∩ S2.carrier
  have h_meas : MeasurableSet E := by
    have h_meas1 : MeasurableSet S1.carrier :=
      isClosed_closedBall.measurableSet.inter isClosed_cthickening.measurableSet
    have h_meas2 : MeasurableSet S2.carrier :=
      isClosed_closedBall.measurableSet.inter isClosed_cthickening.measurableSet
    exact h_meas1.inter h_meas2
  have h_d0 : ∀ (x y : Point3), x ∈ E → y ∈ E → |(A x) 0 - (A y) 0| ≤ 2 := by
    intro x y hx hy
    rw [h_coord x 0, h_coord y 0, h_b0]
    have hx_ball : x ∈ Kakeya.DeltaTube.unitBall := hx.1.1
    have hy_ball : y ∈ Kakeya.DeltaTube.unitBall := hy.1.1
    have hxn : ‖x‖ ≤ 1 := by simpa [Kakeya.DeltaTube.unitBall, Metric.mem_closedBall] using hx_ball
    have hyn : ‖y‖ ≤ 1 := by simpa [Kakeya.DeltaTube.unitBall, Metric.mem_closedBall] using hy_ball
    have h1 : |inner ℝ x v| ≤ 1 := by
      have h : |inner ℝ x v| ≤ ‖x‖ * ‖v‖ := abs_real_inner_le_norm x v
      rw [hv] at h; linarith
    have h2 : |inner ℝ y v| ≤ 1 := by
      have h : |inner ℝ y v| ≤ ‖y‖ * ‖v‖ := abs_real_inner_le_norm y v
      rw [hv] at h; linarith
    calc |inner ℝ x v - inner ℝ y v|
      ≤ |inner ℝ x v| + |inner ℝ y v| := by exact abs_sub _ _
    _ ≤ 1 + 1 := by linarith
    _ = 2 := by norm_num
  have h_bound_s1 : ∀ (z : Point3), z ∈ S1.carrier → |inner ℝ z n1 - S1.offset| ≤ S1.radius := by
    intro z hz
    have h_hyper : S1.hyperplane = {w : Point3 | inner ℝ w n1 = S1.offset} := by
      ext w; simp [Kakeya.Slab.hyperplane, hS1_normal] <;> rfl
    have h_dist : Metric.infDist z S1.hyperplane ≤ S1.radius := by
      have h_ct : z ∈ Metric.cthickening S1.radius S1.hyperplane := hz.2
      have h_ne_top : Metric.infEDist z S1.hyperplane ≠ ⊤ :=
        ne_top_of_le_ne_top (ENNReal.ofReal_ne_top) h_ct
      have h_le : (Metric.infEDist z S1.hyperplane).toReal ≤ (ENNReal.ofReal S1.radius).toReal := by
        rw [ENNReal.toReal_le_toReal h_ne_top (ENNReal.ofReal_ne_top)]
        exact h_ct
      have h_eq : (ENNReal.ofReal S1.radius).toReal = S1.radius := by
        rw [ENNReal.toReal_ofReal S1.radius_nonneg]
      rw [h_eq] at h_le
      exact h_le
    rw [h_hyper] at h_dist
    have h_eq2 : Metric.infDist z {w : Point3 | inner ℝ w n1 = S1.offset} = |inner ℝ z n1 - S1.offset| :=
      dist_to_hyperplane (n := n1) (offset := S1.offset) (x := z) hn1
    rw [h_eq2] at h_dist
    exact h_dist
  have h_d1 : ∀ (x y : Point3), x ∈ E → y ∈ E → |(A x) 1 - (A y) 1| ≤ 2 * S1.radius := by
    intro x y hx hy
    rw [h_coord x 1, h_coord y 1, h_b1]
    have hx1 : |inner ℝ x n1 - S1.offset| ≤ S1.radius := h_bound_s1 x hx.1
    have hy1 : |inner ℝ y n1 - S1.offset| ≤ S1.radius := h_bound_s1 y hy.1
    calc |inner ℝ x n1 - inner ℝ y n1|
      = |(inner ℝ x n1 - S1.offset) - (inner ℝ y n1 - S1.offset)| := by ring_nf
    _ ≤ |inner ℝ x n1 - S1.offset| + |inner ℝ y n1 - S1.offset| := by exact abs_sub _ _
    _ ≤ S1.radius + S1.radius := by linarith
    _ = 2 * S1.radius := by ring
  have h_bound_s2 : ∀ (z : Point3), z ∈ S2.carrier → |inner ℝ z n2 - S2.offset| ≤ S2.radius := by
    intro z hz
    have h_hyper : S2.hyperplane = {w : Point3 | inner ℝ w n2 = S2.offset} := by
      ext w; simp [Kakeya.Slab.hyperplane, hS2_normal] <;> rfl
    have h_dist : Metric.infDist z S2.hyperplane ≤ S2.radius := by
      have h_ct : z ∈ Metric.cthickening S2.radius S2.hyperplane := hz.2
      have h_ne_top : Metric.infEDist z S2.hyperplane ≠ ⊤ :=
        ne_top_of_le_ne_top (ENNReal.ofReal_ne_top) h_ct
      have h_le : (Metric.infEDist z S2.hyperplane).toReal ≤ (ENNReal.ofReal S2.radius).toReal := by
        rw [ENNReal.toReal_le_toReal h_ne_top (ENNReal.ofReal_ne_top)]
        exact h_ct
      have h_eq : (ENNReal.ofReal S2.radius).toReal = S2.radius := by
        rw [ENNReal.toReal_ofReal S2.radius_nonneg]
      rw [h_eq] at h_le
      exact h_le
    rw [h_hyper] at h_dist
    have h_eq2 : Metric.infDist z {w : Point3 | inner ℝ w n2 = S2.offset} = |inner ℝ z n2 - S2.offset| :=
      dist_to_hyperplane (n := n2) (offset := S2.offset) (x := z) hn2
    rw [h_eq2] at h_dist
    exact h_dist
  have h_d2 : ∀ (x y : Point3), x ∈ E → y ∈ E → |(A x) 2 - (A y) 2| ≤ 2 * S2.radius := by
    intro x y hx hy
    rw [h_coord x 2, h_coord y 2, h_b2]
    have hx2 : |inner ℝ x n2 - S2.offset| ≤ S2.radius := h_bound_s2 x hx.2
    have hy2 : |inner ℝ y n2 - S2.offset| ≤ S2.radius := h_bound_s2 y hy.2
    calc |inner ℝ x n2 - inner ℝ y n2|
      = |(inner ℝ x n2 - S2.offset) - (inner ℝ y n2 - S2.offset)| := by ring_nf
    _ ≤ |inner ℝ x n2 - S2.offset| + |inner ℝ y n2 - S2.offset| := by exact abs_sub _ _
    _ ≤ S2.radius + S2.radius := by linarith
    _ = 2 * S2.radius := by ring
  have h_main : volume E ≤ ENNReal.ofReal ((2 : ℝ) * (2 * S1.radius) * (2 * S2.radius)) :=
    Kakeya.Hairbrush.volume_diameter_bound h_meas A 2 (2 * S1.radius) (2 * S2.radius)
      (by norm_num) (by linarith [S1.radius_nonneg]) (by linarith [S2.radius_nonneg]) h_d0 h_d1 h_d2
  have h_final : (2 : ℝ) * (2 * S1.radius) * (2 * S2.radius) ≤ 1000000 * capRadius ^ 2 := by
    have h : (2 : ℝ) * (2 * S1.radius) * (2 * S2.radius) = 8 * S1.radius * S2.radius := by ring
    rw [h]
    have h3 : 0 ≤ S1.radius := S1.radius_nonneg
    have h4 : 0 ≤ S2.radius := S2.radius_nonneg
    nlinarith [hS1_radius, hS2_radius]
  exact h_main.trans (ENNReal.ofReal_le_ofReal h_final)

/-- Triple tube occurrence bound — re-exported from TripleLabelGroupingHelpers. -/
lemma triple_tube_occurrence_bound
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
    (hn12_orth : ∀ j, inner ℝ (n1 j) (n2 j) = 0)
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
    ∑ p ∈ groups, (family p).enncard ≤ 1000000 * F.enncard :=
  tube_occurrence_bound_triple
    (hδ := hδ) (hcap := hcap) (hcap1 := hcap1)
    (hcenter_unit := hcenter_unit)
    (n1 := n1) (n2 := n2)
    (hn1_unit := hn1_unit) (hn2_unit := hn2_unit)
    (hn1_orth := hn1_orth) (hn2_orth := hn2_orth)
    (h_pointwise := h_pointwise)
    (h_label_overlap := h_label_overlap)
    (groups := groups)
    (family := family)
    (h_family_def := h_family_def)

/-! ## Triple-label helpers (allTripleLabels, nonemptyTripleLabels, etc.) are from TripleLabelGroupingHelpers -/

/-! ## Main theorem -/

theorem hairbrush_coarse_tube_incidence_grouping :
    HairbrushCoarseTubeIncidenceGroupingStatement := by
  intro δ eta stopLoss hδ F Y hF_unit angular hmass
  let N := angular.labelCount
  let capRadius := angular.capRadius
  have hcap_pos : 0 < capRadius := by
    have h2 : δ ≤ angular.theta := angular.delta_le_theta
    have h3 : angular.theta ≤ capRadius := angular.theta_le_capRadius
    linarith
  have hcap_le_one : capRadius ≤ 1 := angular.capRadius_le_one
  have hδ_le_cap : δ ≤ capRadius := by
    calc δ ≤ angular.theta := angular.delta_le_theta
         _ ≤ capRadius := angular.theta_le_capRadius

  -- 1. Choose orthonormal frames (v, n1, n2) for each center j
  choose n1 n2 hn1_unit hn2_unit hn1_orth hn2_orth hn12_orth using
    fun j : Fin N => exists_orthonormal_frame (angular.center j) (angular.center_unit j)

  -- 2. Strip labels
  let strip1 : Fin N → Point3 → ℤ := fun j x =>
    Int.floor (inner ℝ x (n1 j) / capRadius)
  let strip2 : Fin N → Point3 → ℤ := fun j x =>
    Int.floor (inner ℝ x (n2 j) / capRadius)

  -- 3. Assignment sets
  let assignSet (j : Fin N) (k1 k2 : ℤ) : Set Point3 :=
    {x | angular.label x = j ∧ strip1 j x = k1 ∧ strip2 j x = k2}

  -- Measurability
  have hassign_meas : ∀ (j : Fin N) (k1 k2 : ℤ), MeasurableSet (assignSet j k1 k2) := by
    intro j k1 k2
    have h1 : MeasurableSet {x : Point3 | angular.label x = j} :=
      angular.label_measurable (MeasurableSet.singleton j)
    have h2 : MeasurableSet {x : Point3 | strip1 j x = k1} :=
      measurable_strip_set (k := k1)
    have h3 : MeasurableSet {x : Point3 | strip2 j x = k2} :=
      measurable_strip_set (k := k2)
    exact h1.inter (h2.inter h3)

  -- 4. Valid triples
  let validTriples : Finset (Fin N × ℤ × ℤ) :=
    nonemptyTripleLabels (capRadius := capRadius) n1 n2 angular.label angular.shading.union

  have hS_ball : angular.shading.union ⊆ Kakeya.DeltaTube.unitBall := by
    intro x hx
    rcases (show ∃ (T : Kakeya.DeltaTube δ), T ∈ F ∧ x ∈ angular.shading.carrier T from by
      simpa [Kakeya.Shading.union] using hx) with ⟨T, hT, hxT⟩
    exact hF_unit hT (angular.shading.subset_tube hT hxT)

  have h_valid_nonempty : validTriples.Nonempty :=
    nonemptyTripleLabels_nonempty hcap_pos n1 n2 hn1_unit hn2_unit angular.label
      angular.shading.union hS_ball
      (shading_mass_nonzero_implies_union_nonempty hmass)

  let groupCount : ℕ := validTriples.card
  have hgroupCount_pos : 0 < groupCount := Finset.Nonempty.card_pos h_valid_nonempty

  -- 5. Enumerate valid triples
  let e : Fin groupCount ≃ {p : Fin N × ℤ × ℤ // p ∈ validTriples} :=
    finsetEquiv validTriples h_valid_nonempty
  let tripleOf : Fin groupCount → Fin N × ℤ × ℤ := fun g => (e g).val
  have htripleOf_inj : Function.Injective tripleOf := by
    intro g1 g2 h
    exact Equiv.injective e (Subtype.ext h)
  have htripleOf_valid : ∀ g, tripleOf g ∈ validTriples := fun g => (e g).property
  have htripleOf_surj : ∀ p ∈ validTriples, ∃ g, tripleOf g = p := by
    intro p hp
    let g : Fin groupCount := e.symm ⟨p, hp⟩
    refine ⟨g, ?_⟩
    simp [g, tripleOf] <;> rfl

  let directionLabel (g : Fin groupCount) : Fin N := (tripleOf g).1
  let stripIndex1 (g : Fin groupCount) : ℤ := (tripleOf g).2.1
  let stripIndex2 (g : Fin groupCount) : ℤ := (tripleOf g).2.2
  let groupSet (g : Fin groupCount) : Set Point3 :=
    assignSet (directionLabel g) (stripIndex1 g) (stripIndex2 g)

  -- 6. Family for each group
  let family (g : Fin groupCount) : Kakeya.TubeFamily δ :=
    F.filter (fun T => ∃ x ∈ angular.shading.carrier T,
      angular.label x = directionLabel g ∧
      strip1 (directionLabel g) x = stripIndex1 g ∧
      strip2 (directionLabel g) x = stripIndex2 g)

  -- Shading for each group
  let shading (g : Fin groupCount) : Kakeya.Shading (family g) :=
    { carrier := fun T => angular.shading.carrier T ∩ groupSet g
      measurable_carrier := fun T hT =>
        (angular.shading.measurable_carrier (Finset.filter_subset _ _ hT)).inter
          (hassign_meas (directionLabel g) (stripIndex1 g) (stripIndex2 g))
      subset_tube := fun T hT =>
        Set.inter_subset_left.trans (angular.shading.subset_tube (Finset.filter_subset _ _ hT)) }

  -- Family subset
  have h_family_sub : ∀ g, family g ⊆ F := fun g => Finset.filter_subset _ _

  -- Family iff
  have h_family_iff : ∀ g T, T ∈ family g ↔
      T ∈ F ∧ ∃ x ∈ angular.shading.carrier T,
        angular.label x = directionLabel g ∧
        strip1 (directionLabel g) x = stripIndex1 g ∧
        strip2 (directionLabel g) x = stripIndex2 g := by
    intro g T
    simp [family, Finset.mem_filter] <;> aesop

  -- Family nonempty
  have h_family_nonempty : ∀ g, (family g).Nonempty := by
    intro g
    have h1 : tripleOf g ∈ validTriples := htripleOf_valid g
    have h2' : (angular.shading.union ∩ {x | angular.label x = (tripleOf g).1 ∧
        strip1 (tripleOf g).1 x = (tripleOf g).2.1 ∧
        strip2 (tripleOf g).1 x = (tripleOf g).2.2}).Nonempty :=
      (Finset.mem_filter.mp h1).2
    have h2 : (angular.shading.union ∩ groupSet g).Nonempty := by
      convert h2' using 2
      <;> simp [groupSet, assignSet, directionLabel, stripIndex1, stripIndex2, strip1, strip2]
      <;> rfl
    rcases h2 with ⟨x, hx_union, hx_set⟩
    rcases (show ∃ (T : Kakeya.DeltaTube δ), T ∈ F ∧ x ∈ angular.shading.carrier T from by
      simpa [Kakeya.Shading.union] using hx_union) with ⟨T, hT, hxT⟩
    have h3 : T ∈ family g := by
      rw [Finset.mem_filter]
      exact ⟨hT, ⟨x, hxT, hx_set.1, hx_set.2.1, hx_set.2.2⟩⟩
    exact ⟨T, h3⟩

  -- Shading carrier empty when T ∈ F and T ∉ family
  have h_shading_empty : ∀ g T, T ∈ F → T ∉ family g → (shading g).carrier T = ∅ := by
    intro g T hT_F hT
    by_contra h
    have h_nonempty : ((shading g).carrier T).Nonempty :=
      Set.nonempty_iff_ne_empty.mpr h
    rcases h_nonempty with ⟨x, hx⟩
    have h_inGroup : ∃ x' ∈ angular.shading.carrier T,
        angular.label x' = directionLabel g ∧
        strip1 (directionLabel g) x' = stripIndex1 g ∧
        strip2 (directionLabel g) x' = stripIndex2 g :=
      ⟨x, hx.1, hx.2.1, hx.2.2.1, hx.2.2.2⟩
    have hT' : T ∈ family g := (h_family_iff g T).mpr ⟨hT_F, h_inGroup⟩
    exact hT hT'

  -- Label consistency
  have h_label_consistency : ∀ g T, ∀ hT : T ∈ family g,
      ∀ x ∈ (shading g).carrier T, angular.label x = directionLabel g := by
    intro g T _ x hx
    exact hx.2.1

  -- Shading subset
  have h_shading_subset : ∀ g T, ∀ hT : T ∈ family g,
      (shading g).carrier T ⊆ angular.shading.carrier T := by
    intro g T _ x hx
    exact hx.1

  -- Angular confinement
  have h_angular_confinement : ∀ g, HairbrushAngularlyConfined (family g) capRadius := by
    intro g
    refine ⟨angular.center (directionLabel g), angular.center_unit (directionLabel g), ?_⟩
    intro T hT
    have h1 := (h_family_iff g T).mp hT
    rcases h1 with ⟨hT_F, x, hxT, hlabel, _, _⟩
    have hx_union : x ∈ angular.shading.union := ⟨T, hT_F, hxT⟩
    have h := angular.pointwise_confined x hx_union T hT_F hxT
    rw [hlabel] at h
    exact h

  -- 7. Two-broadness transfer
  have h_two_broad : ∀ g, IsTwoBroadAtScale (shading g) angular.theta eta := by
    intro g
    let Y_g : Kakeya.Shading F :=
      { carrier := fun T => angular.shading.carrier T ∩ groupSet g
        measurable_carrier := fun T hT =>
          (angular.shading.measurable_carrier hT).inter
            (hassign_meas (directionLabel g) (stripIndex1 g) (stripIndex2 g))
        subset_tube := fun T hT =>
          Set.inter_subset_left.trans (angular.shading.subset_tube hT) }
    have h_broad_g : IsTwoBroadAtScale Y_g angular.theta eta :=
      two_broad_transfer_pointwise angular.two_broad (groupSet g) Y_g
        (fun T _ => rfl)
    have h_carrier : ∀ T ∈ family g, (shading g).carrier T = Y_g.carrier T := by
      intro T _; rfl
    have h_cover : ∀ (x : Point3), x ∈ (shading g).union →
        ∀ T ∈ F, x ∈ Y_g.carrier T → T ∈ family g := by
      intro x hx T hT_F hmem
      rcases Set.mem_setOf.mp hx with ⟨T0, _, hx0⟩
      have hx_set : x ∈ groupSet g := hx0.2
      have hmem1 : x ∈ angular.shading.carrier T := hmem.1
      have h_inGroup : ∃ x' ∈ angular.shading.carrier T,
          angular.label x' = directionLabel g ∧
          strip1 (directionLabel g) x' = stripIndex1 g ∧
          strip2 (directionLabel g) x' = stripIndex2 g :=
        ⟨x, hmem1, hx_set.1, hx_set.2.1, hx_set.2.2⟩
      exact (h_family_iff g T).mpr ⟨hT_F, h_inGroup⟩
    exact two_broad_transfer_subfamily
      (hF'_sub := h_family_sub g)
      (Y := Y_g) (Y' := shading g)
      h_carrier h_cover h_broad_g

  -- 8. Construct slabs directly with known normals, offsets, and radii
  let slab1 (g : Fin groupCount) : Kakeya.Slab :=
    { normal := n1 (directionLabel g)
      offset := (stripIndex1 g : ℝ) * capRadius + capRadius / 2
      radius := 4 * capRadius
      normal_unit := hn1_unit (directionLabel g)
      radius_nonneg := by positivity }
  let slab2 (g : Fin groupCount) : Kakeya.Slab :=
    { normal := n2 (directionLabel g)
      offset := (stripIndex2 g : ℝ) * capRadius + capRadius / 2
      radius := 4 * capRadius
      normal_unit := hn2_unit (directionLabel g)
      radius_nonneg := by positivity }

  -- General slab containment helper
  have h_general_containment : ∀ (g : Fin groupCount) (n : Point3)
      (hn_unit : ‖n‖ = 1) (hn_orth : inner ℝ (angular.center (directionLabel g)) n = 0)
      (k : ℤ) (S : Kakeya.Slab)
      (hS_normal : S.normal = n)
      (hS_offset : S.offset = (k : ℝ) * capRadius + capRadius / 2)
      (hS_radius : S.radius = 4 * capRadius)
      (h_witness : ∀ T ∈ family g, ∃ (x : Point3), x ∈ angular.shading.carrier T ∧
          angular.label x = directionLabel g ∧
          Int.floor (inner ℝ x n / capRadius) = k),
      ∀ T ∈ family g, T.carrier ⊆ S.carrier := by
    intro g n hn_unit hn_orth k S hS_normal hS_offset hS_radius h_witness T hT y hy
    rcases h_witness T hT with ⟨x, hxT, hlabel, hstrip⟩
    have hT_F : T ∈ F := h_family_sub g hT
    have hx_carrier : x ∈ T.carrier := angular.shading.subset_tube hT_F hxT
    have hx_union : x ∈ angular.shading.union := ⟨T, hT_F, hxT⟩
    have hx_ball : x ∈ Kakeya.DeltaTube.unitBall := hF_unit hT_F hx_carrier
    have hy_ball : y ∈ Kakeya.DeltaTube.unitBall := hF_unit hT_F hy
    have h_angle : hairbrushAcuteDirectionAngle T.direction (angular.center (directionLabel g)) ≤ capRadius := by
      have h := angular.pointwise_confined x hx_union T hT_F hxT
      rw [hlabel] at h; exact h
    have h_strip1 : (k : ℝ) ≤ inner ℝ x n / capRadius :=
      Int.le_floor.mp (le_of_eq hstrip.symm)
    have h_strip2 : inner ℝ x n / capRadius < (k : ℝ) + 1 := by
      have h := Int.lt_floor_add_one (inner ℝ x n / capRadius)
      rw [hstrip] at h; exact h
    have h51 : (k : ℝ) * capRadius ≤ inner ℝ x n := by
      have h : (k : ℝ) * capRadius ≤ (inner ℝ x n / capRadius) * capRadius := by gcongr
      have h2 : (inner ℝ x n / capRadius) * capRadius = inner ℝ x n := by
        field_simp [hcap_pos.ne'] <;> ring
      rw [h2] at h; exact h
    have h52 : inner ℝ x n < ((k : ℝ) + 1) * capRadius := by
      have h : (inner ℝ x n / capRadius) * capRadius < ((k : ℝ) + 1) * capRadius := by gcongr
      have h2 : (inner ℝ x n / capRadius) * capRadius = inner ℝ x n := by
        field_simp [hcap_pos.ne'] <;> ring
      rw [h2] at h; exact h
    have h4 : |inner ℝ x n - S.offset| ≤ capRadius / 2 := by
      rw [hS_offset]
      have h13 : inner ℝ x n - ((k : ℝ) * capRadius + capRadius / 2) ≤ capRadius / 2 := by linarith
      have h14 : -(capRadius / 2) ≤ inner ℝ x n - ((k : ℝ) * capRadius + capRadius / 2) := by linarith
      exact abs_le.mpr ⟨h14, h13⟩
    have h_var : |inner ℝ y n - inner ℝ x n| ≤ capRadius + 2 * δ := by
      have h := tube_projection_variation hδ hδ_le_cap hcap_le_one T
        (angular.center (directionLabel g)) n
        (angular.center_unit (directionLabel g)) hn_unit hn_orth h_angle x y hx_carrier hy
      rw [abs_sub_comm] at h
      exact h
    have h5 : |inner ℝ y n - S.offset| ≤ S.radius := by
      calc
        |inner ℝ y n - S.offset|
          = |(inner ℝ y n - inner ℝ x n) + (inner ℝ x n - S.offset)| := by ring_nf
        _ ≤ |inner ℝ y n - inner ℝ x n| + |inner ℝ x n - S.offset| := abs_add_le _ _
        _ ≤ (capRadius + 2 * δ) + capRadius / 2 := by gcongr
        _ ≤ S.radius := by rw [hS_radius] <;> linarith
    have hinner_n : inner ℝ n n = (1 : ℝ) := by
      have h : inner ℝ n n = ‖n‖ ^ 2 := real_inner_self_eq_norm_sq n
      rw [h, hn_unit] <;> norm_num
    have h_H_nonempty : S.hyperplane.Nonempty := by
      have h_off : inner ℝ (S.offset • n) n = S.offset := by
        have h1 : inner ℝ (S.offset • n) n = S.offset * inner ℝ n n := by
          simp [inner_smul_left]
          <;> abel
        rw [h1, hinner_n]
        <;> field_simp
      refine ⟨S.offset • n, ?_⟩
      have h_goal : inner ℝ (S.offset • n) S.normal = S.offset := by
        rw [hS_normal]
        exact h_off
      simpa [Kakeya.Slab.hyperplane] using h_goal
    have h_dist_eq : Metric.infDist y S.hyperplane = |inner ℝ y n - S.offset| := by
      have h_hyperplane : S.hyperplane = {z : Point3 | inner ℝ z n = S.offset} := by
        ext z; simp [Kakeya.Slab.hyperplane, hS_normal] <;> rfl
      rw [h_hyperplane]
      exact dist_to_hyperplane hn_unit
    have h_cthick : y ∈ Metric.cthickening S.radius S.hyperplane := by
      have h6 : Metric.infDist y S.hyperplane ≤ S.radius := by
        rw [h_dist_eq]; exact h5
      have h7 : ENNReal.ofReal (Metric.infDist y S.hyperplane) = Metric.infEDist y S.hyperplane := by
        rw [← ENNReal.ofReal_toReal (Metric.infEDist_ne_top h_H_nonempty)] <;> rfl
      have h8 : Metric.infEDist y S.hyperplane ≤ ENNReal.ofReal S.radius := by
        rw [← h7]; exact ENNReal.ofReal_le_ofReal h6
      exact h8
    exact ⟨hy_ball, h_cthick⟩

  -- Slab containment for n1
  have h_slab1_witness : ∀ (g : Fin groupCount) (T : Kakeya.DeltaTube δ), T ∈ family g →
      ∃ (x : Point3), x ∈ angular.shading.carrier T ∧
        angular.label x = directionLabel g ∧
        Int.floor (inner ℝ x (n1 (directionLabel g)) / capRadius) = stripIndex1 g := by
    intro g T hT
    rcases (h_family_iff g T).mp hT with ⟨hT_F, x, hxT, hlabel, hstrip1, _⟩
    exact ⟨x, hxT, hlabel, hstrip1⟩
  have h_slab1_containment : ∀ g T, T ∈ family g → T.carrier ⊆ (slab1 g).carrier := by
    intro g T hT
    exact h_general_containment g (n1 (directionLabel g))
      (hn1_unit (directionLabel g)) (hn1_orth (directionLabel g))
      (stripIndex1 g) (slab1 g) rfl rfl rfl
      (h_slab1_witness g) T hT

  -- Slab containment for n2
  have h_slab2_witness : ∀ (g : Fin groupCount) (T : Kakeya.DeltaTube δ), T ∈ family g →
      ∃ (x : Point3), x ∈ angular.shading.carrier T ∧
        angular.label x = directionLabel g ∧
        Int.floor (inner ℝ x (n2 (directionLabel g)) / capRadius) = stripIndex2 g := by
    intro g T hT
    rcases (h_family_iff g T).mp hT with ⟨hT_F, x, hxT, hlabel, _, hstrip2⟩
    exact ⟨x, hxT, hlabel, hstrip2⟩
  have h_slab2_containment : ∀ g T, T ∈ family g → T.carrier ⊆ (slab2 g).carrier := by
    intro g T hT
    exact h_general_containment g (n2 (directionLabel g))
      (hn2_unit (directionLabel g)) (hn2_orth (directionLabel g))
      (stripIndex2 g) (slab2 g) rfl rfl rfl
      (h_slab2_witness g) T hT

  -- Slab volume bounds
  have h_slab1_volume : ∀ g, volume (slab1 g).carrier ≤ ENNReal.ofReal (100 * capRadius) := by
    intro g
    have h9 : volume (slab1 g).carrier ≤ ENNReal.ofReal (8 * (slab1 g).radius) := slab_volume_le (slab1 g)
    have h10 : (slab1 g).radius = 4 * capRadius := by rfl
    rw [h10] at h9
    have h11 : (8 * (4 * capRadius) : ℝ) ≤ 100 * capRadius := by linarith
    exact h9.trans (ENNReal.ofReal_le_ofReal h11)
  have h_slab2_volume : ∀ g, volume (slab2 g).carrier ≤ ENNReal.ofReal (100 * capRadius) := by
    intro g
    have h9 : volume (slab2 g).carrier ≤ ENNReal.ofReal (8 * (slab2 g).radius) := slab_volume_le (slab2 g)
    have h10 : (slab2 g).radius = 4 * capRadius := by rfl
    rw [h10] at h9
    have h11 : (8 * (4 * capRadius) : ℝ) ≤ 100 * capRadius := by linarith
    exact h9.trans (ENNReal.ofReal_le_ofReal h11)

  -- 9. Container = intersection of two slab carriers
  let container (g : Fin groupCount) : Set Point3 :=
    (slab1 g).carrier ∩ (slab2 g).carrier

  -- Container convex (unit ball and cthickening of affine subspace are both convex)
  have h_slab_carrier_convex : ∀ (S : Kakeya.Slab), Convex ℝ S.carrier := by
    intro S
    have h1 : Convex ℝ Kakeya.DeltaTube.unitBall := by
      exact convex_closedBall (0 : Point3) 1
    have h_hyperplane_convex : Convex ℝ S.hyperplane := by
      have h : S.hyperplane = {z : Point3 | inner ℝ z S.normal = S.offset} := by
        ext z; simp [Kakeya.Slab.hyperplane] <;> rfl
      rw [h]
      let f : Point3 →ₗ[ℝ] ℝ :=
        { toFun := fun z => inner ℝ z S.normal
          map_add' := by intro u v; simp [inner_add_left]
          map_smul' := by intro c u; simp [inner_smul_left] }
      have h_conv : Convex ℝ ({S.offset} : Set ℝ) := convex_singleton _
      exact h_conv.linear_preimage f
    have h2 : Convex ℝ (Metric.cthickening S.radius S.hyperplane) :=
      h_hyperplane_convex.cthickening _
    exact h1.inter h2
  have h_container_convex : ∀ g, Convex ℝ (container g) := by
    intro g
    exact (h_slab_carrier_convex (slab1 g)).inter (h_slab_carrier_convex (slab2 g))

  -- Container containment
  have h_container_containment : ∀ g T, T ∈ family g → T.carrier ⊆ container g := by
    intro g T hT
    have h1 : T.carrier ⊆ (slab1 g).carrier := h_slab1_containment g T hT
    have h2 : T.carrier ⊆ (slab2 g).carrier := h_slab2_containment g T hT
    exact Set.subset_inter h1 h2

  -- Container volume (uses missing helper)
  have h_container_volume : ∀ g,
      volume (container g) ≤ ENNReal.ofReal (1000000 * capRadius ^ 2) := by
    intro g
    have h_r1 : (slab1 g).radius = 4 * capRadius := by rfl
    have h_r2 : (slab2 g).radius = 4 * capRadius := by rfl
    have h_n1 : (slab1 g).normal = n1 (directionLabel g) := by rfl
    have h_n2 : (slab2 g).normal = n2 (directionLabel g) := by rfl
    exact two_slab_container_volume hcap_pos
      (angular.center (directionLabel g)) (n1 (directionLabel g)) (n2 (directionLabel g))
      (angular.center_unit (directionLabel g))
      (hn1_unit (directionLabel g)) (hn2_unit (directionLabel g))
      (hn1_orth (directionLabel g)) (hn2_orth (directionLabel g))
      (hn12_orth (directionLabel g))
      (slab1 g) (slab2 g)
      h_n1 h_n2 (by rw [h_r1]) (by rw [h_r2])

  -- 10. Group sets pairwise disjoint
  have h_groupset_disj : ∀ g1 g2, g1 ≠ g2 → Disjoint (groupSet g1) (groupSet g2) := by
    intro g1 g2 hne
    rw [Set.disjoint_left]
    intro x hx1 hx2
    have h1 : angular.label x = directionLabel g1 := hx1.1
    have h2 : angular.label x = directionLabel g2 := hx2.1
    have h3 : directionLabel g1 = directionLabel g2 := h1.symm.trans h2
    have h4 : strip1 (directionLabel g1) x = stripIndex1 g1 := hx1.2.1
    have h5 : strip1 (directionLabel g2) x = stripIndex1 g2 := hx2.2.1
    rw [h3] at h4
    have h6 : stripIndex1 g1 = stripIndex1 g2 := h4.symm.trans h5
    have h7 : strip2 (directionLabel g1) x = stripIndex2 g1 := hx1.2.2
    have h8 : strip2 (directionLabel g2) x = stripIndex2 g2 := hx2.2.2
    rw [h3] at h7
    have h9 : stripIndex2 g1 = stripIndex2 g2 := h7.symm.trans h8
    have h10 : tripleOf g1 = tripleOf g2 := by
      apply Prod.ext
      · exact h3
      · apply Prod.ext
        · exact h6
        · exact h9
    have h11 : g1 = g2 := htripleOf_inj h10
    exact hne h11

  -- Disjoint unions
  have h_union_disjoint : ∀ g1 g2, g1 ≠ g2 →
      Disjoint (shading g1).union (shading g2).union := by
    intro g1 g2 hne
    rw [Set.disjoint_left]
    intro x hx1 hx2
    rcases hx1 with ⟨T1, hT1, hxT1⟩
    rcases hx2 with ⟨T2, hT2, hxT2⟩
    have h1 : angular.label x = directionLabel g1 := hxT1.2.1
    have h2 : angular.label x = directionLabel g2 := hxT2.2.1
    have h3 : directionLabel g1 = directionLabel g2 := h1.symm.trans h2
    have h4 : strip1 (directionLabel g1) x = stripIndex1 g1 := hxT1.2.2.1
    have h5 : strip1 (directionLabel g2) x = stripIndex1 g2 := hxT2.2.2.1
    rw [h3] at h4
    have h6 : stripIndex1 g1 = stripIndex1 g2 := h4.symm.trans h5
    have h7 : strip2 (directionLabel g1) x = stripIndex2 g1 := hxT1.2.2.2
    have h8 : strip2 (directionLabel g2) x = stripIndex2 g2 := hxT2.2.2.2
    rw [h3] at h7
    have h9 : stripIndex2 g1 = stripIndex2 g2 := h7.symm.trans h8
    have h10 : tripleOf g1 = tripleOf g2 := by
      apply Prod.ext
      · exact h3
      · apply Prod.ext
        · exact h6
        · exact h9
    have h11 : g1 = g2 := htripleOf_inj h10
    exact hne h11

  -- Helper: valid triple from point
  have h_point_valid : ∀ (x : Point3), x ∈ angular.shading.union →
      let j := angular.label x
      let k1 := strip1 j x
      let k2 := strip2 j x
      (j, k1, k2) ∈ validTriples := by
    intro x hx
    let j := angular.label x
    let k1 := strip1 j x
    let k2 := strip2 j x
    rcases (show ∃ (T : Kakeya.DeltaTube δ), T ∈ F ∧ x ∈ angular.shading.carrier T from by
      simpa [Kakeya.Shading.union] using hx) with ⟨T, hT, hxT⟩
    have hx_ball : x ∈ Kakeya.DeltaTube.unitBall :=
      hF_unit hT (angular.shading.subset_tube hT hxT)
    have h_all : (j, k1, k2) ∈ allTripleLabels capRadius :=
      point_witnesses_triple hcap_pos n1 n2 hn1_unit hn2_unit angular.label
        angular.shading.union x hx hx_ball j rfl
    have h_nonempty : (angular.shading.union ∩ {x | angular.label x = j ∧
        strip1 j x = k1 ∧ strip2 j x = k2}).Nonempty :=
      ⟨x, hx, by simp [j, k1, k2]⟩
    have h_in_filter : (j, k1, k2) ∈ validTriples := by
      have h_def : validTriples = nonemptyTripleLabels (capRadius := capRadius) n1 n2 angular.label angular.shading.union := by rfl
      rw [h_def, nonemptyTripleLabels, Finset.mem_filter]
      exact ⟨h_all, h_nonempty⟩
    exact h_in_filter

  -- Exact union
  have h_union_exact : (⋃ g, (shading g).union) = angular.shading.union := by
    apply Set.Subset.antisymm
    · intro x hx
      rcases Set.mem_iUnion.mp hx with ⟨g, hxg⟩
      rcases hxg with ⟨T, hT, hxT⟩
      have hT_F : T ∈ F := h_family_sub g hT
      exact ⟨T, hT_F, hxT.1⟩
    · intro x hx
      rcases (show ∃ (T : Kakeya.DeltaTube δ), T ∈ F ∧ x ∈ angular.shading.carrier T from by
        simpa [Kakeya.Shading.union] using hx) with ⟨T, hT, hxT⟩
      let j := angular.label x
      let k1 := strip1 j x
      let k2 := strip2 j x
      have h_pair_valid : (j, k1, k2) ∈ validTriples := h_point_valid x hx
      rcases htripleOf_surj (j, k1, k2) h_pair_valid with ⟨g, hg⟩
      have hdir : directionLabel g = j := by
        exact congr_arg (fun p : Fin N × ℤ × ℤ => p.1) hg
      have hstrip1 : stripIndex1 g = k1 := by
        exact congr_arg (fun p : Fin N × ℤ × ℤ => p.2.1) hg
      have hstrip2 : stripIndex2 g = k2 := by
        exact congr_arg (fun p : Fin N × ℤ × ℤ => p.2.2) hg
      have hT_fam : T ∈ family g := by
        have h_inGroup : ∃ x' ∈ angular.shading.carrier T,
            angular.label x' = directionLabel g ∧
            strip1 (directionLabel g) x' = stripIndex1 g ∧
            strip2 (directionLabel g) x' = stripIndex2 g := by
          refine ⟨x, hxT, ?_⟩
          constructor
          · exact hdir.symm
          · constructor
            · rw [hdir, hstrip1] <;> rfl
            · rw [hdir, hstrip2] <;> rfl
        exact (h_family_iff g T).mpr ⟨hT, h_inGroup⟩
      have hxg_set : x ∈ groupSet g := by
        simp [groupSet, assignSet, directionLabel, stripIndex1, stripIndex2, hdir, hstrip1, hstrip2] <;> exact ⟨rfl, rfl, rfl⟩
      have hx_shading : x ∈ (shading g).carrier T := by
        have h_eq : (shading g).carrier T = angular.shading.carrier T ∩ groupSet g := by rfl
        rw [h_eq]; exact ⟨hxT, hxg_set⟩
      have hxg : x ∈ (shading g).union := ⟨T, hT_fam, hx_shading⟩
      exact Set.mem_iUnion.mpr ⟨g, hxg⟩

  -- 11. Mass additivity
  have h_mass_additive : ∑ g, (shading g).mass = angular.shading.mass :=
    incidence_mass_additivity
      (Y := angular.shading)
      (assignSet := fun g => groupSet g)
      (hassign_meas := fun g => hassign_meas (directionLabel g) (stripIndex1 g) (stripIndex2 g))
      (hassign_disj := h_groupset_disj)
      (hassign_cover := by
        intro x hx
        let j := angular.label x
        let k1 := strip1 j x
        let k2 := strip2 j x
        have h_pair_valid : (j, k1, k2) ∈ validTriples := h_point_valid x hx
        rcases htripleOf_surj (j, k1, k2) h_pair_valid with ⟨g, hg⟩
        have hdir : directionLabel g = j := congr_arg (fun p : Fin N × ℤ × ℤ => p.1) hg
        have hstrip1 : stripIndex1 g = k1 := congr_arg (fun p : Fin N × ℤ × ℤ => p.2.1) hg
        have hstrip2 : stripIndex2 g = k2 := congr_arg (fun p : Fin N × ℤ × ℤ => p.2.2) hg
        have hxg : x ∈ groupSet g := by
          dsimp only [groupSet, assignSet]
          exact ⟨hdir.symm, by rw [hdir, hstrip1] <;> rfl, by rw [hdir, hstrip2] <;> rfl⟩
        exact Set.mem_iUnion.mpr ⟨g, hxg⟩)
      (family := family)
      (hfamily_sub := h_family_sub)
      (shading := shading)
      (hshading_eq := fun g T _ => rfl)
      (hzero := h_shading_empty)

  -- 12. Tube occurrence bound (triple version)
  let family' : (Fin N × ℤ × ℤ) → Kakeya.TubeFamily δ := fun p =>
    F.filter (fun T => ∃ x ∈ angular.shading.carrier T,
      angular.label x = p.1 ∧
      Int.floor (inner ℝ x (n1 p.1) / capRadius) = p.2.1 ∧
      Int.floor (inner ℝ x (n2 p.1) / capRadius) = p.2.2)
  have h_family'_def : ∀ p, family' p = F.filter (fun T =>
      ∃ x ∈ angular.shading.carrier T, angular.label x = p.1 ∧
        Int.floor (inner ℝ x (n1 p.1) / capRadius) = p.2.1 ∧
        Int.floor (inner ℝ x (n2 p.1) / capRadius) = p.2.2) := by
    intro p; rfl
  have h_family_eq : ∀ g, family g = family' (tripleOf g) := by
    intro g
    apply Finset.ext
    intro T
    simp [family, family', directionLabel, stripIndex1, stripIndex2, strip1, strip2] <;> rfl
  have h_sum_eq : ∑ g : Fin groupCount, (family g).enncard =
      ∑ p ∈ validTriples, (family' p).enncard := by
    have h1 : ∑ g : Fin groupCount, (family g).enncard =
        ∑ g : Fin groupCount, (family' (tripleOf g)).enncard := by
      apply Finset.sum_congr rfl
      intro g _
      rw [h_family_eq g]
    have h2 : ∑ g : Fin groupCount, (family' (tripleOf g)).enncard =
        ∑ p ∈ validTriples, (family' p).enncard := by
      have h3 : ∑ g : Fin groupCount, (family' (tripleOf g)).enncard =
          ∑ p : {p : Fin N × ℤ × ℤ // p ∈ validTriples}, (family' (p : Fin N × ℤ × ℤ)).enncard := by
        apply Fintype.sum_equiv e
        intro g
        rfl
      rw [h3]
      exact (Finset.sum_subtype validTriples (fun _ => Iff.rfl) (fun p => (family' p).enncard)).symm
    rw [h1, h2]
  have h_occurrence : ∑ g, (family g).enncard ≤ 1000000 * F.enncard := by
    rw [h_sum_eq]
    exact triple_tube_occurrence_bound
      (hδ := hδ) (hcap := hδ_le_cap) (hcap1 := hcap_le_one)
      (hcenter_unit := angular.center_unit)
      (n1 := n1) (n2 := n2)
      (hn1_unit := hn1_unit) (hn2_unit := hn2_unit)
      (hn1_orth := hn1_orth) (hn2_orth := hn2_orth) (hn12_orth := hn12_orth)
      (h_pointwise := angular.pointwise_confined)
      (h_label_overlap := angular.label_overlap)
      (groups := validTriples)
      (family := family')
      (h_family_def := h_family'_def)

  -- 13. Assemble HairbrushSlabIncidenceGroupingData
  let grouping : HairbrushSlabIncidenceGroupingData angular :=
    { groupCount := groupCount
      groupCount_pos := hgroupCount_pos
      family := family
      shading := shading
      family_nonempty := h_family_nonempty
      family_subset := h_family_sub
      directionLabel := directionLabel
      label_consistency := h_label_consistency
      shading_subset := h_shading_subset
      angular_confinement := h_angular_confinement
      two_broad := h_two_broad
      slab := slab1
      slab_containment := h_slab1_containment
      slab_volume := h_slab1_volume
      union_disjoint := h_union_disjoint
      union_exact := h_union_exact
      incidence_mass_additive := h_mass_additive
      tube_occurrence_bound := h_occurrence }

  -- 14. Assemble HairbrushCoarseTubeIncidenceGroupingData
  exact ⟨grouping, container, h_container_convex, h_container_volume,
    h_container_containment⟩

end Kakeya.Assouad

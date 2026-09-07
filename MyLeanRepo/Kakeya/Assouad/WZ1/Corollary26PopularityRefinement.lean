-- import MyLeanRepo.Kakeya.Assouad.WZ1.AreaBoundCorollary  -- TODO: re-enable when AD-bound lemma compiles
import MyLeanRepo.Kakeya.Assouad.LargeSlope.ADSlabVolumeBound
import MyLeanRepo.Kakeya.Assouad.WZ1.Definitions
import MyLeanRepo.Kakeya.Assouad.WZ1.AnchoredHierarchyHelpers
import MyLeanRepo.Kakeya.Assouad.WZ1.AnchoredHierarchyIteration
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-!
# Popularity refinement and endpoint anchoring for WZ1 Corollary 26

This module implements:
1. Measure-to-span conversion: if a measurable set in ℝ has measure > L,
   it contains two points at distance > L.
2. Shading thinning: remove mass at heights belonging to unpopular trapezoid cores.
3. Volume-in-core estimates via Fubini and horizontal slice area bounds.
4. Single-level popularity selection.
5. Descending multi-level refinement.
6. Endpoint anchoring using shrink_trapezoid_to_active_endpoints.
-/

noncomputable section

open MeasureTheory Set Metric Finset ENNReal

namespace Kakeya.Assouad

/-! ## 1. Measure-to-span conversion -/

/--
If a measurable set A ⊆ ℝ has measure > L, then there exist a, b ∈ A
with b - a > L.

Uses `Real.volume_le_diam` and `Metric.ediam_le_of_forall_dist_le`.
-/
lemma measure_implies_distance {A : Set ℝ} {L : ℝ} (_hL : 0 ≤ L)
    (_hA : MeasurableSet A) (hvol : volume A > ENNReal.ofReal L) :
    ∃ (a b : ℝ), a ∈ A ∧ b ∈ A ∧ b - a > L := by
  by_contra h
  push Not at h
  have h_dist : ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ L := by
    intro x hx y hy
    have h1 : y - x ≤ L := h x y hx hy
    have h2 : x - y ≤ L := h y x hy hx
    have h3 : |x - y| ≤ L := by
      rw [abs_le]; constructor <;> linarith
    simpa [Real.dist_eq] using h3
  have h_ediam : Metric.ediam A ≤ ENNReal.ofReal L :=
    Metric.ediam_le_of_forall_dist_le h_dist
  have h_vol_le : volume A ≤ Metric.ediam A := Real.volume_le_diam A
  have h_final : volume A ≤ ENNReal.ofReal L := h_vol_le.trans h_ediam
  exact not_le.mpr hvol h_final

/-! ## 2. Shading thinning -/

/-- Thin a shading by removing all points whose height belongs to a set H. -/
def thinShading {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    (Z : Kakeya.Streamlined.TubeShading F) (H : Set ℝ)
    (hH_meas : MeasurableSet H) :
    Kakeya.Streamlined.TubeShading F :=
  let heightMap : Point3 → ℝ := fun p => p 2
  have h_height_meas : Measurable heightMap := by
    have h_cont : Continuous heightMap :=
      PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 2
    exact h_cont.measurable
  { carrier := fun i => Z.carrier i \ heightMap ⁻¹' H
    measurable_carrier := fun i =>
      (Z.measurable_carrier i).diff (h_height_meas hH_meas)
    subset_body := fun i =>
      Set.Subset.trans (fun x hx => hx.1) (Z.subset_body i) }

/-- The thinned shading is a subshading of the original. -/
lemma thinShading_subshading {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    {Z : Kakeya.Streamlined.TubeShading F} {H : Set ℝ} {hH_meas : MeasurableSet H} :
    IsSubshading (thinShading Z H hH_meas) Z := by
  intro i x hx
  exact hx.1

/-- Union of thinned shading. -/
lemma thinShading_union {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    {Z : Kakeya.Streamlined.TubeShading F} {H : Set ℝ} {hH_meas : MeasurableSet H} :
    (thinShading Z H hH_meas).union = Z.union \ {p : Point3 | p 2 ∈ H} := by
  ext p
  simp only [thinShading, Kakeya.Streamlined.Shading.union, Set.mem_sdiff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨i, ⟨h1, h2⟩⟩
    exact ⟨⟨i, h1⟩, h2⟩
  · rintro ⟨⟨i, h1⟩, h2⟩
    exact ⟨i, ⟨h1, h2⟩⟩

/-- Point multiplicity is preserved by horizontal thinning.

If `p` survives the thinning (`p 2 ∉ H`), then every tube of `Z` containing `p`
also contains `p` in the thinned shading, so the point multiplicity is unchanged. -/
lemma thinShading_same_multiplicity {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    {Z : Kakeya.Streamlined.TubeShading F} {H : Set ℝ} {hH_meas : MeasurableSet H}
    {p : Point3} (hp : p ∈ (thinShading Z H hH_meas).union) :
    (thinShading Z H hH_meas).pointMultiplicity p = Z.pointMultiplicity p := by
  classical
  have hpH : p 2 ∉ H := by
    have h : p ∈ (thinShading Z H hH_meas).union := hp
    rw [thinShading_union] at h
    exact h.2
  have h1 : ∀ (i : Fin F.card), p ∈ (thinShading Z H hH_meas).carrier i ↔ p ∈ Z.carrier i := by
    intro i
    simp only [thinShading, Set.mem_diff]
    exact ⟨fun h => h.1, fun h => ⟨h, hpH⟩⟩
  have h_eq : (Finset.univ.filter fun i : Fin F.card => p ∈ (thinShading Z H hH_meas).carrier i) =
      (Finset.univ.filter fun i : Fin F.card => p ∈ Z.carrier i) := by
    apply Finset.ext
    intro i
    simpa using h1 i
  have h_main : (thinShading Z H hH_meas).pointMultiplicity p = Z.pointMultiplicity p := by
    unfold Kakeya.Streamlined.Shading.pointMultiplicity
    exact congr_arg Finset.card h_eq
  exact h_main

/-! ## 3. Volume-in-core -/

/-- Volume of the shaded union inside a horizontal slab [a, b]. -/
def volumeInSlab {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    (Z : Kakeya.Streamlined.TubeShading F) (a b : ℝ) : ENNReal :=
  MeasureTheory.volume (Z.union ∩ {p : Point3 | p 2 ∈ Set.Icc a b})

/-- Volume of the shaded union inside a trapezoid core. -/
def volumeInCore {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    (Z : Kakeya.Streamlined.TubeShading F)
    (t : WZ1VerticalTrapezoid) : ENNReal :=
  volumeInSlab Z t.left t.right

/--
Volume-in-core bound via product diameter:
`volumeInCore Z t ≤ 4 * ediam(activeSet Z ∩ t.core)`.

Since Z.union ⊆ unitBall, the x and y projections have diameter ≤ 2.
By `Real.volume_pi_le_prod_diam`, the 3D volume is bounded by the product
of the three coordinate diameters.
-/
lemma volumeInCore_le_ediam_active
    {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    {Z : Kakeya.Streamlined.TubeShading F}
    (hZ_ball : Z.union ⊆ Kakeya.DeltaTube.unitBall)
    (t : WZ1VerticalTrapezoid) :
    volumeInCore Z t ≤ 4 * Metric.ediam (activeSet Z ∩ t.core) := by
  let S : Set Point3 := Z.union ∩ {p | p 2 ∈ t.core}
  have h1 : volumeInCore Z t = volume S := by rfl
  rw [h1]
  -- S is measurable
  have hS_meas : MeasurableSet S := by
    have h_union_eq : Z.union = ⋃ i : Fin F.card, Z.carrier i := by
      ext x
      simp [Kakeya.Streamlined.Shading.union]
      <;> rfl
    have h_union_meas : MeasurableSet Z.union := by
      rw [h_union_eq]
      exact MeasurableSet.iUnion (fun i => Z.measurable_carrier i)
    have h_height_meas : MeasurableSet {p : Point3 | p 2 ∈ t.core} := by
      have h_cont : Continuous (fun p : Point3 => p 2) :=
        PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 2
      exact h_cont.measurable measurableSet_Icc
    exact h_union_meas.inter h_height_meas
  -- Convert Point3 to Fin 3 → ℝ via WithLp.ofLp
  let F_equiv : Point3 ≃ᵐ (Fin 3 → ℝ) :=
    { toFun := WithLp.ofLp (p := 2)
      invFun := WithLp.toLp (p := 2)
      left_inv := WithLp.toLp_ofLp (p := 2)
      right_inv := WithLp.ofLp_toLp (p := 2)
      measurable_toFun := (PiLp.volume_preserving_ofLp (ι := Fin 3)).measurable
      measurable_invFun := (PiLp.continuous_toLp 2 (β := fun (_ : Fin 3) => ℝ)).measurable }
  let F_map : Point3 → (Fin 3 → ℝ) := F_equiv
  let S' : Set (Fin 3 → ℝ) := F_map '' S
  have hpres : MeasurePreserving F_map volume volume :=
    PiLp.volume_preserving_ofLp (ι := Fin 3)
  have hvol : volume S = volume S' := by
    have hmap : Measure.map F_map volume = volume := hpres.map_eq
    have hpre : F_map ⁻¹' S' = S := Set.preimage_image_eq _ F_equiv.injective
    have hS'_meas : MeasurableSet S' := F_equiv.measurableSet_image.mpr hS_meas
    have h2 : volume (F_map ⁻¹' S') = Measure.map F_map volume S' :=
      (Measure.map_apply hpres.measurable hS'_meas).symm
    rw [hpre] at h2
    exact h2.trans (by rw [hmap])
  rw [hvol]
  have h2 : volume S' ≤ ∏ i : Fin 3, Metric.ediam (Function.eval i '' S') :=
    Real.volume_pi_le_prod_diam S'
  -- Coordinate projections of S' equal coordinate projections of S
  have hproj : ∀ (i : Fin 3), (Function.eval i '' S') = (fun p : Point3 => p i) '' S := by
    intro i
    ext x
    simp only [Set.mem_image, S']
    constructor
    · rintro ⟨q, ⟨p, hp, rfl⟩, rfl⟩
      exact ⟨p, hp, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨F_map p, ⟨p, hp, rfl⟩, rfl⟩
  -- Coordinate bound: |p i| ≤ 1 for p ∈ S
  have h_coord_bound : ∀ (i : Fin 3), ∀ p ∈ S, |p i| ≤ 1 := by
    intro i p hp
    have h5 : p ∈ Z.union := hp.1
    have h6 : p ∈ Kakeya.DeltaTube.unitBall := hZ_ball h5
    have h7 : ‖p‖ ≤ 1 := by simpa [Kakeya.DeltaTube.unitBall] using h6
    let e_i : Point3 := EuclideanSpace.single i (1 : ℝ)
    have h9 : inner ℝ p e_i = p i := by
      rw [EuclideanSpace.inner_single_right]
      <;> simp [e_i]
    have h10 : |inner ℝ p e_i| ≤ ‖p‖ * ‖e_i‖ := abs_real_inner_le_norm p e_i
    have h11 : ‖e_i‖ = 1 := by
      simp [e_i, PiLp.norm_single]
    rw [h9, h11] at h10
    have h12 : |p i| ≤ ‖p‖ := by simpa using h10
    linarith
  have h_ediam_bound : ∀ (i : Fin 3), Metric.ediam ((fun p : Point3 => p i) '' S) ≤ 2 := by
    intro i
    have h9 : ((fun p : Point3 => p i) '' S) ⊆ Set.Icc (-1 : ℝ) 1 := by
      intro x hx
      rcases hx with ⟨p, hp, rfl⟩
      have h10 : |p i| ≤ 1 := h_coord_bound i p hp
      have h11 : -1 ≤ p i ∧ p i ≤ 1 := by
        rw [abs_le] at h10
        exact h10
      exact ⟨h11.1, h11.2⟩
    have h12 : ∀ (x : ℝ), x ∈ ((fun p : Point3 => p i) '' S) →
        ∀ (y : ℝ), y ∈ ((fun p : Point3 => p i) '' S) → dist x y ≤ 2 := by
      intro x hx y hy
      have h13 : x ∈ Set.Icc (-1 : ℝ) 1 := h9 hx
      have h14 : y ∈ Set.Icc (-1 : ℝ) 1 := h9 hy
      have h15 : -1 ≤ x := h13.1
      have h16 : x ≤ 1 := h13.2
      have h17 : -1 ≤ y := h14.1
      have h18 : y ≤ 1 := h14.2
      have h19 : |x - y| ≤ 2 := by
        rw [abs_le]
        constructor <;> linarith
      simpa [Real.dist_eq] using h19
    have h15 : Metric.ediam ((fun p : Point3 => p i) '' S) ≤ ENNReal.ofReal 2 :=
      Metric.ediam_le_of_forall_dist_le h12
    simpa using h15
  have h3 : Metric.ediam (Function.eval 0 '' S') ≤ 2 := by
    rw [hproj 0]; exact h_ediam_bound 0
  have h4 : Metric.ediam (Function.eval 1 '' S') ≤ 2 := by
    rw [hproj 1]; exact h_ediam_bound 1
  have h5 : Metric.ediam (Function.eval 2 '' S') = Metric.ediam (activeSet Z ∩ t.core) := by
    rw [hproj 2]
    congr
    ext z
    simp only [Set.mem_image, activeSet, S, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨p, ⟨hp1, hp2⟩, rfl⟩
      have hz_active : horizontalSlice Z.union (p 2) ≠ ∅ := by
        have hpin : p ∈ horizontalSlice Z.union (p 2) := by
          simp [horizontalSlice, hp1]
        exact Set.nonempty_iff_ne_empty.mp ⟨p, hpin⟩
      exact ⟨hz_active, hp2⟩
    · rintro ⟨hz_active, hz_core⟩
      have hne : (horizontalSlice Z.union z).Nonempty :=
        Set.nonempty_iff_ne_empty.mpr hz_active
      rcases hne with ⟨p, hp⟩
      have hp1 : p ∈ Z.union := by
        simp only [horizontalSlice, Set.mem_setOf_eq] at hp
        exact hp.1
      have hp2 : p 2 = z := by
        simp only [horizontalSlice, Set.mem_setOf_eq] at hp
        exact hp.2
      have hp3 : p 2 ∈ t.core := by rw [hp2] <;> exact hz_core
      exact ⟨p, ⟨hp1, hp3⟩, hp2⟩
  have h_prod : (∏ i : Fin 3, Metric.ediam (Function.eval i '' S')) =
      Metric.ediam (Function.eval 0 '' S') *
      Metric.ediam (Function.eval 1 '' S') *
      Metric.ediam (Function.eval 2 '' S') := by
    simp [Fin.prod_univ_succ] <;> ring
  rw [h_prod] at h2
  rw [h5] at h2
  have h_mul : Metric.ediam (Function.eval 0 '' S') * Metric.ediam (Function.eval 1 '' S') ≤ (4 : ENNReal) := by
    calc
      Metric.ediam (Function.eval 0 '' S') * Metric.ediam (Function.eval 1 '' S')
        ≤ (2 : ENNReal) * Metric.ediam (Function.eval 1 '' S') := by gcongr
      _ ≤ (2 : ENNReal) * (2 : ENNReal) := by gcongr
      _ = (4 : ENNReal) := by norm_num
  have h6 : (Metric.ediam (Function.eval 0 '' S') *
      Metric.ediam (Function.eval 1 '' S') *
      Metric.ediam (activeSet Z ∩ t.core)) ≤
      4 * Metric.ediam (activeSet Z ∩ t.core) := by
    have h8 : (Metric.ediam (Function.eval 0 '' S') * Metric.ediam (Function.eval 1 '' S')) * Metric.ediam (activeSet Z ∩ t.core) ≤
        (4 : ENNReal) * Metric.ediam (activeSet Z ∩ t.core) :=
      mul_le_mul_right' h_mul (Metric.ediam (activeSet Z ∩ t.core))
    simpa [mul_assoc] using h8
  exact h2.trans h6

/-! ## 4b. Unit-ball slab volume bound -/

/-- Volume of a unit-ball-contained set in a horizontal slab is at most `4 * (b - a)`.
The x and y coordinates each have diameter at most 2. -/
lemma unitBall_slab_volume_bound
    {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    {Z : Kakeya.Streamlined.TubeShading F}
    (hZ_ball : Z.union ⊆ Kakeya.DeltaTube.unitBall)
    {a b : ℝ} (ha : a ≤ b) :
    MeasureTheory.volume (Z.union ∩ horizontalSlab a b) ≤
      (4 : ENNReal) * ENNReal.ofReal (b - a) := by
  let S : Set Point3 := Z.union ∩ horizontalSlab a b
  have hS_meas : MeasurableSet S := by
    have h_union_eq : Z.union = ⋃ i : Fin F.card, Z.carrier i := by
      ext x; simp [Kakeya.Streamlined.Shading.union] <;> rfl
    have h_union_meas : MeasurableSet Z.union := by
      rw [h_union_eq]; exact MeasurableSet.iUnion (fun i => Z.measurable_carrier i)
    have h_cont : Continuous (fun p : Point3 => p 2) := PiLp.continuous_apply 2 (fun _ => ℝ) 2
    have h_slab_meas : MeasurableSet (horizontalSlab a b) := h_cont.measurable measurableSet_Icc
    exact h_union_meas.inter h_slab_meas
  let F_equiv : Point3 ≃ᵐ (Fin 3 → ℝ) :=
    { toFun := WithLp.ofLp (p := 2)
      invFun := WithLp.toLp (p := 2)
      left_inv := WithLp.toLp_ofLp (p := 2)
      right_inv := WithLp.ofLp_toLp (p := 2)
      measurable_toFun := (PiLp.volume_preserving_ofLp (ι := Fin 3)).measurable
      measurable_invFun := (PiLp.continuous_toLp 2 (β := fun (_ : Fin 3) => ℝ)).measurable }
  let S' : Set (Fin 3 → ℝ) := F_equiv '' S
  have hpres : MeasurePreserving F_equiv volume volume := PiLp.volume_preserving_ofLp (ι := Fin 3)
  have hvol : volume S = volume S' := by
    have hmap : Measure.map F_equiv volume = volume := hpres.map_eq
    have hpre : F_equiv ⁻¹' S' = S := Set.preimage_image_eq _ F_equiv.injective
    have hS'_meas : MeasurableSet S' := F_equiv.measurableSet_image.mpr hS_meas
    have h2 : volume (F_equiv ⁻¹' S') = Measure.map F_equiv volume S' :=
      (Measure.map_apply hpres.measurable hS'_meas).symm
    rw [hpre] at h2; exact h2.trans (by rw [hmap])
  rw [hvol]
  have h2 : volume S' ≤ ∏ i : Fin 3, Metric.ediam (Function.eval i '' S') :=
    Real.volume_pi_le_prod_diam S'
  have hproj : ∀ (i : Fin 3), (Function.eval i '' S') = (fun p : Point3 => p i) '' S := by
    intro i
    ext x
    simp only [Set.mem_image, S']
    constructor
    · rintro ⟨q, ⟨p, hp, hq⟩, h_eq⟩
      have h_eval : Function.eval i q = p i := by
        have h_q_eq : q = F_equiv p := hq.symm
        rw [h_q_eq] <;> rfl
      have h_goal : p i = x := h_eval.symm.trans h_eq
      exact ⟨p, hp, h_goal⟩
    · rintro ⟨p, hp, h_eq⟩
      have h_eval : Function.eval i (F_equiv p) = p i := by rfl
      refine ⟨F_equiv p, ⟨p, hp, rfl⟩, ?_⟩
      exact h_eval.trans h_eq
  have h_coord_bound : ∀ (i : Fin 3), ∀ p ∈ S, |p i| ≤ 1 := by
    intro i p hp
    have h5 : p ∈ Z.union := hp.1
    have h6 : p ∈ Kakeya.DeltaTube.unitBall := hZ_ball h5
    have h7 : ‖p‖ ≤ 1 := by simpa [Kakeya.DeltaTube.unitBall] using h6
    let e_i : Point3 := EuclideanSpace.single i (1 : ℝ)
    have h9 : inner ℝ p e_i = p i := by rw [EuclideanSpace.inner_single_right] <;> simp [e_i]
    have h10 : |inner ℝ p e_i| ≤ ‖p‖ * ‖e_i‖ := abs_real_inner_le_norm p e_i
    have h11 : ‖e_i‖ = 1 := by simp [e_i, PiLp.norm_single]
    rw [h9, h11] at h10
    have h12 : |p i| ≤ ‖p‖ := by simpa using h10
    exact h12.trans h7
  have h_ediam_xy : ∀ (i : Fin 3), i = 0 ∨ i = 1 → Metric.ediam ((fun p : Point3 => p i) '' S) ≤ 2 := by
    intro i hi
    have h9 : ((fun p : Point3 => p i) '' S) ⊆ Set.Icc (-1 : ℝ) 1 := by
      intro x hx; rcases hx with ⟨p, hp, rfl⟩
      have h10 : |p i| ≤ 1 := h_coord_bound i p hp
      rw [abs_le] at h10; exact ⟨h10.1, h10.2⟩
    have h12 : ∀ (x : ℝ), x ∈ ((fun p : Point3 => p i) '' S) →
        ∀ (y : ℝ), y ∈ ((fun p : Point3 => p i) '' S) → dist x y ≤ 2 := by
      intro x hx y hy
      have h13 : x ∈ Set.Icc (-1 : ℝ) 1 := h9 hx
      have h14 : y ∈ Set.Icc (-1 : ℝ) 1 := h9 hy
      simp only [Set.mem_Icc] at h13 h14
      have h15 : |x - y| ≤ 2 := by rw [abs_le]; constructor <;> linarith
      simpa [Real.dist_eq] using h15
    have h15 : Metric.ediam ((fun p : Point3 => p i) '' S) ≤ ENNReal.ofReal 2 :=
      Metric.ediam_le_of_forall_dist_le h12
    simpa using h15
  have h_z_bound : Metric.ediam ((fun p : Point3 => p 2) '' S) ≤ ENNReal.ofReal (b - a) := by
    have h9 : ∀ (z : ℝ), z ∈ ((fun p : Point3 => p 2) '' S) → z ∈ Set.Icc a b := by
      intro z hz; rcases hz with ⟨p, hp, rfl⟩
      have h10 : p ∈ horizontalSlab a b := hp.2
      simpa [horizontalSlab, Set.mem_setOf_eq] using h10
    have h12 : ∀ (x : ℝ), x ∈ ((fun p : Point3 => p 2) '' S) →
        ∀ (y : ℝ), y ∈ ((fun p : Point3 => p 2) '' S) → dist x y ≤ b - a := by
      intro x hx y hy
      have h13 : x ∈ Set.Icc a b := h9 x hx
      have h14 : y ∈ Set.Icc a b := h9 y hy
      simp only [Set.mem_Icc] at h13 h14
      have h15 : |x - y| ≤ b - a := by rw [abs_le]; constructor <;> linarith
      simpa [Real.dist_eq] using h15
    exact Metric.ediam_le_of_forall_dist_le h12
  have h3 : Metric.ediam (Function.eval 0 '' S') ≤ 2 := by rw [hproj 0]; exact h_ediam_xy 0 (Or.inl rfl)
  have h4 : Metric.ediam (Function.eval 1 '' S') ≤ 2 := by rw [hproj 1]; exact h_ediam_xy 1 (Or.inr rfl)
  have h5 : Metric.ediam (Function.eval 2 '' S') ≤ ENNReal.ofReal (b - a) := by rw [hproj 2]; exact h_z_bound
  have h6 : (∏ i : Fin 3, Metric.ediam (Function.eval i '' S')) ≤
      (2 : ENNReal) * (2 : ENNReal) * ENNReal.ofReal (b - a) := by
    have h7 : ∏ i : Fin 3, Metric.ediam (Function.eval i '' S') =
        Metric.ediam (Function.eval 0 '' S') *
        Metric.ediam (Function.eval 1 '' S') *
        Metric.ediam (Function.eval 2 '' S') := by
      simp [Fin.prod_univ_succ] <;> ring
    rw [h7]; gcongr <;> assumption
  have h8 : (2 : ENNReal) * (2 : ENNReal) * ENNReal.ofReal (b - a) = (4 : ENNReal) * ENNReal.ofReal (b - a) := by ring
  rw [h8] at h6
  exact h2.trans h6

/-! ## 5. Single-level popularity selection -/

/--
Construct a shrunk trapezoid whose left and right endpoints are given
active points.
-/
def shrinkTrapezoidToPoints
    (t : WZ1VerticalTrapezoid)
    (a b : ℝ) (hab : a < b)
    (ha_in : a ∈ t.core) (hb_in : b ∈ t.core) :
    WZ1VerticalTrapezoid :=
  { left := a
    right := b
    left_lt_right := hab
    slope := t.slope
    intercept := t.intercept
    height := t.height
    height_pos := t.height_pos }

lemma shrinkTrapezoidToPoints_spec
    (t : WZ1VerticalTrapezoid)
    (a b : ℝ) (hab : a < b)
    (ha_in : a ∈ t.core) (hb_in : b ∈ t.core) :
    let t' := shrinkTrapezoidToPoints t a b hab ha_in hb_in
    t'.core ⊆ t.core ∧
    t'.left = a ∧ t'.right = b ∧
    t'.slope = t.slope ∧
    t'.intercept = t.intercept ∧
    t'.height = t.height := by
  dsimp only [shrinkTrapezoidToPoints]
  constructor
  · intro z hz
    have h1 : a ≤ z := (Set.mem_Icc.mp hz).1
    have h2 : z ≤ b := (Set.mem_Icc.mp hz).2
    have h3 : t.left ≤ a := (Set.mem_Icc.mp ha_in).1
    have h4 : b ≤ t.right := (Set.mem_Icc.mp hb_in).2
    exact Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- If one trapezoid's core is contained in another's, its length is smaller. -/
lemma trapezoid_length_mono {t t' : WZ1VerticalTrapezoid}
    (h : t'.core ⊆ t.core) : t'.length ≤ t.length := by
  have h1 : t.left ≤ t'.left := by
    have h2 : t'.left ∈ t'.core := Set.left_mem_Icc.mpr t'.left_lt_right.le
    have h3 : t'.left ∈ t.core := h h2
    exact (Set.mem_Icc.mp h3).1
  have h4 : t'.right ≤ t.right := by
    have h5 : t'.right ∈ t'.core := Set.right_mem_Icc.mpr t'.left_lt_right.le
    have h6 : t'.right ∈ t.core := h h5
    exact (Set.mem_Icc.mp h6).2
  have h7 : t'.length = t'.right - t'.left := by rfl
  have h8 : t.length = t.right - t.left := by rfl
  rw [h7, h8]
  linarith

/--
Given a volume lower bound on the shaded union inside a trapezoid core,
and an upper bound A_max on the area of each horizontal slice, prove
there exist active heights a,b in the core with b-a > L.
-/
lemma active_points_from_volume
    {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    {Z : Kakeya.Streamlined.TubeShading F}
    {t : WZ1VerticalTrapezoid}
    {A_max : ENNReal} {L : ℝ} (hL_pos : 0 ≤ L)
    (h_vol : volume (Z.union ∩ horizontalSlab t.left t.right) >
      A_max * ENNReal.ofReal L)
    (h_slab_bound : ∀ (a b : ℝ), a ≤ b →
      volume (Z.union ∩ horizontalSlab a b) ≤ A_max * ENNReal.ofReal (b - a)) :
    ∃ (a b : ℝ), a ∈ activeSet Z ∩ t.core ∧
      b ∈ activeSet Z ∩ t.core ∧ b - a > L := by
  let A : Set ℝ := activeSet Z ∩ t.core
  have hA_nonempty : A.Nonempty := by
    by_contra h
    have h' : A = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    have h_empty : Z.union ∩ horizontalSlab t.left t.right = ∅ := by
      ext p
      simp only [Set.mem_empty_iff_false, Set.mem_setOf_eq, iff_false]
      intro hp
      have hz : p 2 ∈ t.core := by
        simp only [horizontalSlab, Set.mem_setOf_eq] at hp <;> exact hp.2
      have h_active : p 2 ∈ activeSet Z := by
        have hslice : p ∈ horizontalSlice Z.union (p 2) := by
          simp [horizontalSlice, hp.1]
        exact Set.nonempty_iff_ne_empty.mp ⟨p, hslice⟩
      have h_in_A : p 2 ∈ A := ⟨h_active, hz⟩
      rw [h'] at h_in_A <;> simp at h_in_A
    rw [h_empty] at h_vol
    simp at h_vol <;> exact h_vol
  let i : ℝ := sInf A
  let s : ℝ := sSup A
  have h_bdd_below : BddBelow A := ⟨t.left, fun x hx => (Set.mem_Icc.mp hx.2).1⟩
  have h_bdd_above : BddAbove A := ⟨t.right, fun x hx => (Set.mem_Icc.mp hx.2).2⟩
  have h1 : ∀ x ∈ A, i ≤ x := fun x hx => csInf_le h_bdd_below hx
  have h2 : ∀ x ∈ A, x ≤ s := fun x hx => le_csSup h_bdd_above hx
  by_cases h_span : s - i ≤ L
  · have h3 : A ⊆ Set.Icc i (i + L) := by
      intro x hx
      have h4 : i ≤ x := h1 x hx
      have h5 : x ≤ s := h2 x hx
      have h6 : x ≤ i + L := by linarith
      exact ⟨h4, h6⟩
    have h4 : Z.union ∩ horizontalSlab t.left t.right ⊆
        Z.union ∩ horizontalSlab i (i + L) := by
      intro p hp
      have hz : p 2 ∈ t.core := by
        simp only [horizontalSlab, Set.mem_setOf_eq] at hp <;> exact hp.2
      have h_active : p 2 ∈ activeSet Z := by
        have hslice : p ∈ horizontalSlice Z.union (p 2) := by
          simp [horizontalSlice, hp.1]
        exact Set.nonempty_iff_ne_empty.mp ⟨p, hslice⟩
      have h_in_A : p 2 ∈ A := ⟨h_active, hz⟩
      have h5 : p 2 ∈ Set.Icc i (i + L) := h3 h_in_A
      exact ⟨hp.1, by simpa [horizontalSlab] using h5⟩
    have h5 : volume (Z.union ∩ horizontalSlab t.left t.right) ≤
        volume (Z.union ∩ horizontalSlab i (i + L)) := measure_mono h4
    have h6 : i ≤ i + L := by linarith
    have h7 : volume (Z.union ∩ horizontalSlab i (i + L)) ≤
        A_max * ENNReal.ofReal L := by
      have h8 := h_slab_bound i (i + L) h6
      have h9 : (i + L) - i = L := by ring
      rw [h9] at h8
      exact h8
    have h10 : volume (Z.union ∩ horizontalSlab t.left t.right) ≤
        A_max * ENNReal.ofReal L := le_trans h5 h7
    exfalso
    exact not_le.mpr h_vol h10
  · have h_span' : s - i > L := by linarith
    have h_exists_a : ∃ (a : ℝ), a ∈ A ∧ a < i + (s - i - L) / 2 := by
      by_contra h
      have h_all : ∀ x ∈ A, i + (s - i - L) / 2 ≤ x := by
        simpa [not_exists, not_and, not_lt] using h
      have h_i_ge : i + (s - i - L) / 2 ≤ i :=
        le_csInf hA_nonempty h_all
      linarith
    have h_exists_b : ∃ (b : ℝ), b ∈ A ∧ b > s - (s - i - L) / 2 := by
      by_contra h
      have h_all : ∀ x ∈ A, x ≤ s - (s - i - L) / 2 := by
        simpa [not_exists, not_and, not_lt] using h
      have h_s_le : s ≤ s - (s - i - L) / 2 :=
        csSup_le hA_nonempty h_all
      linarith
    rcases h_exists_a with ⟨a, haA, ha_lt⟩
    rcases h_exists_b with ⟨b, hbA, hb_gt⟩
    have h_diff : b - a > L := by linarith
    exact ⟨a, b, haA, hbA, h_diff⟩

/--
Single-level popularity selection and endpoint anchoring.

Given a shading Z and trapezoids T, select trapezoids with sufficient
volume in their core, shrink them to active endpoints, and thin Z
to retain only heights covered by shrunk popular cores.

Output:
- Z': thinned shading
- T': shrunk popular trapezoids
- Every t' ∈ T' has active endpoints in Z'
- Every t' ∈ T' has length ≥ L
- Coverage: every active height of Z' lies in some t' core
- Each t' comes from some original t ∈ T
-
Helper: if z is active in Z and z is not in the removed height set H,
then z remains active in the thinned shading Z'.
-/
lemma active_height_preserved
    {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    {Z Z' : Kakeya.Streamlined.TubeShading F} {H : Set ℝ}
    (hZ'_union : Z'.union = Z.union \ {p : Point3 | p 2 ∈ H})
    {z : ℝ} (hz_active : z ∈ activeSet Z) (hz_notin_H : z ∉ H) :
    z ∈ activeSet Z' := by
  have h_ne : (horizontalSlice Z.union z).Nonempty :=
    Set.nonempty_iff_ne_empty.mpr hz_active
  rcases h_ne with ⟨p, hp⟩
  have hpZ : p ∈ Z.union := by
    simp only [horizontalSlice, Set.mem_setOf_eq] at hp <;> exact hp.1
  have hpz : p 2 = z := by
    simp only [horizontalSlice, Set.mem_setOf_eq] at hp <;> exact hp.2
  have hpinZ' : p ∈ Z'.union := by
    rw [hZ'_union]
    have h2 : p 2 ∉ H := by rw [hpz]; exact hz_notin_H
    exact ⟨hpZ, h2⟩
  have hslice : p ∈ horizontalSlice Z'.union z := by
    simp only [horizontalSlice, Set.mem_setOf_eq] <;> exact ⟨hpinZ', hpz⟩
  exact Set.nonempty_iff_ne_empty.mp ⟨p, hslice⟩

lemma single_level_popularity_refine
    {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    {Z : Kakeya.Streamlined.TubeShading F}
    {T : Finset WZ1VerticalTrapezoid}
    {A_max : ENNReal} {L : ℝ}
    (hL_pos : 0 ≤ L)
    (h_slab_bound : ∀ (a b : ℝ), a ≤ b →
      volume (Z.union ∩ horizontalSlab a b) ≤ A_max * ENNReal.ofReal (b - a)) :
    ∃ (Z' : Kakeya.Streamlined.TubeShading F)
      (T' : Finset WZ1VerticalTrapezoid),
      IsSubshading Z' Z ∧
      (∀ t' ∈ T', horizontalSlice Z'.union t'.left ≠ ∅ ∧
                        horizontalSlice Z'.union t'.right ≠ ∅) ∧
      (∀ t' ∈ T', L ≤ t'.length) ∧
      (∀ t' ∈ T', ∃ t ∈ T,
        t'.core ⊆ t.core ∧ t'.slope = t.slope ∧ t'.intercept = t.intercept ∧ t'.height = t.height) ∧
      (∀ (z : ℝ), horizontalSlice Z'.union z ≠ ∅ →
        ∃ t' ∈ T', z ∈ t'.core) ∧
      (∀ p ∈ Z'.union, Z'.pointMultiplicity p = Z.pointMultiplicity p) := by
  classical
  let popular : Finset WZ1VerticalTrapezoid :=
    T.filter (fun t => volumeInCore Z t > A_max * ENNReal.ofReal L)
  have h_popular_iff : ∀ t, t ∈ popular ↔
      t ∈ T ∧ volumeInCore Z t > A_max * ENNReal.ofReal L := by
    intro t; simp [popular] <;> tauto
  -- Choose endpoints for each popular trapezoid
  let P (t : WZ1VerticalTrapezoid) : Prop :=
    ∃ (a b : ℝ), a ∈ activeSet Z ∩ t.core ∧
      b ∈ activeSet Z ∩ t.core ∧ b - a > L
  have h_main : ∀ t ∈ popular, P t := by
    intro t ht
    have h_vol : volumeInCore Z t > A_max * ENNReal.ofReal L :=
      (h_popular_iff t).mp ht |>.2
    exact active_points_from_volume hL_pos h_vol h_slab_bound
  choose a b ha hb hdiff using h_main
  let shrunk (t : WZ1VerticalTrapezoid) : WZ1VerticalTrapezoid :=
    if ht : t ∈ popular then
      shrinkTrapezoidToPoints t (a t ht) (b t ht)
        (by linarith [hdiff t ht]) (ha t ht).2 (hb t ht).2
    else t
  let T' : Finset WZ1VerticalTrapezoid := popular.image shrunk
  let popularCores : Set ℝ := ⋃ t' ∈ T', t'.core
  have h_popularCores_meas : MeasurableSet popularCores := by
    have h : (T' : Set WZ1VerticalTrapezoid).Countable := Set.to_countable _
    exact MeasurableSet.biUnion h (fun t' _ => measurableSet_Icc)
  let H : Set ℝ := popularCoresᶜ
  have hH_meas : MeasurableSet H := h_popularCores_meas.compl
  let Z' : Kakeya.Streamlined.TubeShading F := thinShading Z H hH_meas
  have hZ'_sub : IsSubshading Z' Z := thinShading_subshading
  have hZ'_union : Z'.union = Z.union \ {p : Point3 | p 2 ∈ H} := thinShading_union
  -- Shrunk trapezoid properties
  have h_shrunk_spec : ∀ (t : WZ1VerticalTrapezoid) (ht : t ∈ popular),
      (shrunk t).left = a t ht ∧ (shrunk t).right = b t ht ∧
      (shrunk t).core ⊆ t.core ∧ (shrunk t).slope = t.slope ∧
      (shrunk t).intercept = t.intercept ∧
      (shrunk t).height = t.height ∧ L ≤ (shrunk t).length := by
    intro t ht
    dsimp only [shrunk]
    rw [dif_pos ht]
    have h_spec := shrinkTrapezoidToPoints_spec t (a t ht) (b t ht)
      (by linarith [hdiff t ht]) (ha t ht).2 (hb t ht).2
    have h_len : L ≤ (b t ht) - (a t ht) := le_of_lt (hdiff t ht)
    exact ⟨h_spec.2.1, h_spec.2.2.1, h_spec.1, h_spec.2.2.2.1, h_spec.2.2.2.2.1, h_spec.2.2.2.2.2, h_len⟩
  have h_coverage : ∀ (z : ℝ), horizontalSlice Z'.union z ≠ ∅ →
      ∃ t' ∈ T', z ∈ t'.core := by
    intro z hz
    have h_z_in_popularCores : z ∈ popularCores := by
      by_contra h
      have hz' : z ∈ H := h
      have h_empty : horizontalSlice Z'.union z = ∅ := by
        ext p
        simp only [Set.mem_empty_iff_false, iff_false]
        intro hp
        have hpe : p ∈ Z'.union ∧ p 2 = z := by
          simp only [horizontalSlice, Set.mem_setOf_eq] at hp <;> exact hp
        rw [hZ'_union] at hpe
        have h2 : p 2 ∉ H := hpe.1.2
        rw [hpe.2] at h2
        exact h2 hz'
      rw [h_empty] at hz <;> simp at hz
    simp only [popularCores, Set.mem_iUnion] at h_z_in_popularCores
    rcases h_z_in_popularCores with ⟨t', ht', hzcore⟩
    exact ⟨t', ht', hzcore⟩
  -- Active endpoints
  have h_active_endpoints : ∀ t' ∈ T',
      horizontalSlice Z'.union t'.left ≠ ∅ ∧
      horizontalSlice Z'.union t'.right ≠ ∅ := by
    intro t' ht'
    rcases Finset.mem_image.mp ht' with ⟨t, ht, rfl⟩
    have h_spec := h_shrunk_spec t ht
    have h_at_active : a t ht ∈ activeSet Z := (ha t ht).1
    have h_bt_active : b t ht ∈ activeSet Z := (hb t ht).1
    have h_at_in_core : a t ht ∈ (shrunk t).core := by
      have h : (shrunk t).left = a t ht := h_spec.1
      rw [←h]
      exact ⟨le_refl _, (shrunk t).left_lt_right.le⟩
    have h_bt_in_core : b t ht ∈ (shrunk t).core := by
      have h : (shrunk t).right = b t ht := h_spec.2.1
      rw [←h]
      exact ⟨(shrunk t).left_lt_right.le, le_refl _⟩
    have h_st_in_T' : shrunk t ∈ T' := by
      exact Finset.mem_image_of_mem shrunk ht
    have h_at_in_pc : a t ht ∈ popularCores := by
      simpa [popularCores, Set.mem_iUnion] using ⟨shrunk t, h_st_in_T', h_at_in_core⟩
    have h_bt_in_pc : b t ht ∈ popularCores := by
      simpa [popularCores, Set.mem_iUnion] using ⟨shrunk t, h_st_in_T', h_bt_in_core⟩
    have h_at_notin_H : a t ht ∉ H := by
      simpa [H] using h_at_in_pc
    have h_bt_notin_H : b t ht ∉ H := by
      simpa [H] using h_bt_in_pc
    have h_at_active' : a t ht ∈ activeSet Z' :=
      active_height_preserved hZ'_union h_at_active h_at_notin_H
    have h_bt_active' : b t ht ∈ activeSet Z' :=
      active_height_preserved hZ'_union h_bt_active h_bt_notin_H
    have h_left_eq : (shrunk t).left = a t ht := h_spec.1
    have h_right_eq : (shrunk t).right = b t ht := h_spec.2.1
    constructor
    · rw [h_left_eq]; exact h_at_active'
    · rw [h_right_eq]; exact h_bt_active'
  -- Length bounds
  have h_length : ∀ t' ∈ T', L ≤ t'.length := by
    intro t' ht'
    rcases Finset.mem_image.mp ht' with ⟨t, ht, rfl⟩
    rcases h_shrunk_spec t ht with ⟨_, _, _, _, _, _, h_len⟩
    exact h_len
  have h_provenance : ∀ t' ∈ T', ∃ t ∈ T,
      t'.core ⊆ t.core ∧ t'.slope = t.slope ∧ t'.intercept = t.intercept ∧ t'.height = t.height := by
    intro t' ht'
    rcases Finset.mem_image.mp ht' with ⟨t, ht, rfl⟩
    have h_t_in_T : t ∈ T := (h_popular_iff t).mp ht |>.1
    rcases h_shrunk_spec t ht with ⟨_, _, h_core, h_slope, h_int, h_hgt, _⟩
    exact ⟨t, h_t_in_T, h_core, h_slope, h_int, h_hgt⟩
  exact ⟨Z', T', hZ'_sub, h_active_endpoints, h_length, h_provenance, h_coverage,
    fun p hp => thinShading_same_multiplicity hp⟩

/-! ## 7. Unique parent from active endpoints + coverage -/

/--
Given all hierarchy properties except `unique_parent`, plus `active_endpoints`,
prove the `unique_parent` property.

Uses `numerical_nesting_from_endpoint_approximations` from
`AnchoredHierarchyIteration`.  The child's active endpoints, together with
parent-level coverage, ensure the child's left and right endpoints lie in
some parent core.  Slope approximation at the active endpoints extends to
the whole core because the difference of affine functions is affine.
-/
lemma hierarchy_unique_parent
    {N : ℕ} {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {sourceSlope : ℝ → ℝ} {hierarchyLoss : ℝ}
    {trapezoids : Fin N → Finset WZ1VerticalTrapezoid}
    (hdelta_pos : 0 < delta)
    (hdelta_le_one : delta ≤ 1)
    (hY_ball : Y.union ⊆ Metric.closedBall (0 : Point3) 1)
    (h_height_eq : ∀ (j : Fin N), ∀ t ∈ trapezoids j,
      t.height = wz1Corollary26Scale delta N j)
    (h_length_bounds : ∀ (j : Fin N), ∀ t ∈ trapezoids j,
      t.length ≤ Real.sqrt (wz1Corollary26Scale delta N j))
    (h_length_lower : ∀ (j : Fin N), ∀ t ∈ trapezoids j,
      Real.rpow (wz1Corollary26Scale delta N j) (1 / 2 + hierarchyLoss) ≤ t.length)
    (h_separated_cores : ∀ (j : Fin N),
      ∀ t ∈ trapezoids j, ∀ s ∈ trapezoids j, t ≠ s →
        ∀ z ∈ t.core, ∀ w ∈ s.core,
          Real.sqrt (wz1Corollary26Scale delta N j) ≤ |z - w|)
    (h_slope_approximation : ∀ (j : Fin N),
      ∀ t ∈ trapezoids j, ∀ z ∈ t.core,
        horizontalSlice Y.union z ≠ ∅ →
          |sourceSlope z - t.affine z| ≤ wz1Corollary26Scale delta N j)
    (h_active_height_coverage : ∀ (j : Fin N),
      ∀ z ∈ Set.Icc (-1 : ℝ) 1,
        horizontalSlice Y.union z ≠ ∅ → ∃ t ∈ trapezoids j, z ∈ t.core)
    (h_active_endpoints : ∀ (j : Fin N), ∀ t ∈ trapezoids j,
      horizontalSlice Y.union t.left ≠ ∅ ∧
        horizontalSlice Y.union t.right ≠ ∅)
    (h_level_nonempty : ∀ (j : Fin N), (trapezoids j).Nonempty) :
    ∀ (parentLevel childLevel : Fin N),
      (parentLevel : ℕ) + 1 = (childLevel : ℕ) →
        ∀ child ∈ trapezoids childLevel,
          ∃! (parent : WZ1VerticalTrapezoid),
            parent ∈ trapezoids parentLevel ∧
              child.IsNumericallyNestedIn parent := by
  intro parentLevel childLevel h_succ child hchild
  let rho_parent := wz1Corollary26Scale delta N parentLevel
  let rho_child := wz1Corollary26Scale delta N childLevel
  have h_rho_parent_pos : 0 < rho_parent := Real.rpow_pos_of_pos hdelta_pos _
  have h_rho_child_pos : 0 < rho_child := Real.rpow_pos_of_pos hdelta_pos _
  have h_child_length : child.length ≤ Real.sqrt rho_child :=
    h_length_bounds childLevel child hchild
  have h_child_height : child.height = rho_child :=
    h_height_eq childLevel child hchild
  have h_parent_heights : ∀ p ∈ trapezoids parentLevel, p.height = rho_parent :=
    fun p hp => h_height_eq parentLevel p hp
  have h_child_left_active : horizontalSlice Y.union child.left ≠ ∅ :=
    (h_active_endpoints childLevel child hchild).1
  have h_child_right_active : horizontalSlice Y.union child.right ≠ ∅ :=
    (h_active_endpoints childLevel child hchild).2
  have h_child_left_in_Icc : child.left ∈ Set.Icc (-1 : ℝ) 1 :=
    anchored_active_height_in_Icc hY_ball h_child_left_active
  have h_child_right_in_Icc : child.right ∈ Set.Icc (-1 : ℝ) 1 :=
    anchored_active_height_in_Icc hY_ball h_child_right_active
  have h_left_covered : ∃ p ∈ trapezoids parentLevel, child.left ∈ p.core :=
    h_active_height_coverage parentLevel child.left h_child_left_in_Icc h_child_left_active
  have h_right_covered : ∃ p ∈ trapezoids parentLevel, child.right ∈ p.core :=
    h_active_height_coverage parentLevel child.right h_child_right_in_Icc h_child_right_active
  by_cases hdelta_lt_one : delta < 1
  · -- Case delta < 1: scales strictly decrease, use unique_parent_core_containment
    have h_child_lt_parent : rho_child < rho_parent := by
      have h1 : (parentLevel : ℕ) < (childLevel : ℕ) := by omega
      have h_raw := hierarchyScale_strict_mono hdelta_pos hdelta_lt_one h1 childLevel.isLt
      have h_eq_c := hierarchyScale_eq_wz1Scale (delta := delta) (N := N) (j := childLevel)
      have h_eq_p := hierarchyScale_eq_wz1Scale (delta := delta) (N := N) (j := parentLevel)
      rw [h_eq_c, h_eq_p] at h_raw
      exact h_raw
    have h_unique_core := unique_parent_core_containment
      h_rho_parent_pos h_rho_child_pos
      (h_separated_cores parentLevel)
      h_child_length h_child_lt_parent
      h_left_covered h_right_covered
    rcases h_unique_core with ⟨p, ⟨hp_mem, h_core_sub⟩, h_uniq⟩
    have h_left_in_p : child.left ∈ p.core :=
      h_core_sub (Set.left_mem_Icc.mpr child.left_lt_right.le)
    have h_right_in_p : child.right ∈ p.core :=
      h_core_sub (Set.right_mem_Icc.mpr child.left_lt_right.le)
    have h_child_approx_left := h_slope_approximation childLevel child hchild child.left
      (Set.left_mem_Icc.mpr child.left_lt_right.le) h_child_left_active
    have h_child_approx_right := h_slope_approximation childLevel child hchild child.right
      (Set.right_mem_Icc.mpr child.left_lt_right.le) h_child_right_active
    have h_parent_approx_left := h_slope_approximation parentLevel p hp_mem child.left
      h_left_in_p h_child_left_active
    have h_parent_approx_right := h_slope_approximation parentLevel p hp_mem child.right
      h_right_in_p h_child_right_active
    have h_nesting := numerical_nesting_from_endpoint_approximations
      h_child_height (h_parent_heights p hp_mem) h_core_sub
      h_child_approx_left h_child_approx_right
      h_parent_approx_left h_parent_approx_right
    refine ⟨p, ⟨hp_mem, h_nesting⟩, ?_⟩
    intro q hq
    have hq_core_sub : child.core ⊆ q.core := hq.2.1
    exact h_uniq q ⟨hq.1, hq_core_sub⟩
  · -- Case delta = 1: all scales are 1, at most one trapezoid per level
    have hdelta_eq : delta = 1 := by linarith
    have h_rho_eq1 : ∀ (j : Fin N), wz1Corollary26Scale delta N j = 1 := by
      intro j
      rw [hdelta_eq]
      simp [wz1Corollary26Scale] <;> norm_num
    have h_len1 : ∀ (j : Fin N), ∀ t ∈ trapezoids j, t.length = 1 := by
      intro j t ht
      have hlb := h_length_bounds j t ht
      have hll := h_length_lower j t ht
      have hr : wz1Corollary26Scale delta N j = 1 := h_rho_eq1 j
      rw [hr] at hlb hll
      have h1 : Real.rpow (1 : ℝ) (1 / 2 + hierarchyLoss) = 1 := by simp
      have h2 : Real.sqrt (1 : ℝ) = 1 := by simp
      rw [h1] at hll
      rw [h2] at hlb
      linarith
    have h_cores_in_Icc : ∀ (j : Fin N), ∀ t ∈ trapezoids j, t.core ⊆ Set.Icc (-1 : ℝ) 1 := by
      intro j t ht
      have h_left_Icc : t.left ∈ Set.Icc (-1 : ℝ) 1 :=
        anchored_active_height_in_Icc hY_ball (h_active_endpoints j t ht).1
      have h_right_Icc : t.right ∈ Set.Icc (-1 : ℝ) 1 :=
        anchored_active_height_in_Icc hY_ball (h_active_endpoints j t ht).2
      intro z hz
      have h1 : t.left ≤ z := (Set.mem_Icc.mp hz).1
      have h2 : z ≤ t.right := (Set.mem_Icc.mp hz).2
      exact Set.mem_Icc.mpr ⟨by linarith [(Set.mem_Icc.mp h_left_Icc).1, (Set.mem_Icc.mp h_right_Icc).1],
        by linarith [(Set.mem_Icc.mp h_left_Icc).2, (Set.mem_Icc.mp h_right_Icc).2]⟩
    have h_sep1 : ∀ (j : Fin N), ∀ t ∈ trapezoids j, ∀ s ∈ trapezoids j, t ≠ s →
        ∀ z ∈ t.core, ∀ w ∈ s.core, (1 : ℝ) ≤ |z - w| := by
      intro j t ht s hs hne z hz w hw
      have h := h_separated_cores j t ht s hs hne z hz w hw
      have hr : wz1Corollary26Scale delta N j = 1 := h_rho_eq1 j
      rw [hr] at h
      have hsqrt1 : Real.sqrt (1 : ℝ) = 1 := by norm_num
      rw [hsqrt1] at h
      exact h
    have h_at_most_one : ∀ (j : Fin N), ∀ t ∈ trapezoids j, ∀ s ∈ trapezoids j, t = s :=
      fun j => at_most_one_trapezoid_delta_one (h_len1 j) (h_sep1 j) (h_cores_in_Icc j)
    rcases h_level_nonempty parentLevel with ⟨parent, hp_mem⟩
    have h_parent_unique : ∀ q ∈ trapezoids parentLevel, q = parent :=
      fun q hq => h_at_most_one parentLevel q hq parent hp_mem
    have h_core_sub : child.core ⊆ parent.core := by
      rcases h_left_covered with ⟨p_left, hp_left_mem, h_left_in⟩
      have hp_left_eq : p_left = parent := h_parent_unique p_left hp_left_mem
      rw [hp_left_eq] at h_left_in
      rcases h_right_covered with ⟨p_right, hp_right_mem, h_right_in⟩
      have hp_right_eq : p_right = parent := h_parent_unique p_right hp_right_mem
      rw [hp_right_eq] at h_right_in
      intro z hz
      have h1 : child.left ≤ z := (Set.mem_Icc.mp hz).1
      have h2 : z ≤ child.right := (Set.mem_Icc.mp hz).2
      have h3 : parent.left ≤ child.left := (Set.mem_Icc.mp h_left_in).1
      have h4 : child.right ≤ parent.right := (Set.mem_Icc.mp h_right_in).2
      exact Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
    have h_left_in_p : child.left ∈ parent.core :=
      h_core_sub (Set.left_mem_Icc.mpr child.left_lt_right.le)
    have h_right_in_p : child.right ∈ parent.core :=
      h_core_sub (Set.right_mem_Icc.mpr child.left_lt_right.le)
    have h_child_approx_left := h_slope_approximation childLevel child hchild child.left
      (Set.left_mem_Icc.mpr child.left_lt_right.le) h_child_left_active
    have h_child_approx_right := h_slope_approximation childLevel child hchild child.right
      (Set.right_mem_Icc.mpr child.left_lt_right.le) h_child_right_active
    have h_parent_approx_left := h_slope_approximation parentLevel parent hp_mem child.left
      h_left_in_p h_child_left_active
    have h_parent_approx_right := h_slope_approximation parentLevel parent hp_mem child.right
      h_right_in_p h_child_right_active
    have h_nesting := numerical_nesting_from_endpoint_approximations
      h_child_height (h_parent_heights parent hp_mem) h_core_sub
      h_child_approx_left h_child_approx_right
      h_parent_approx_left h_parent_approx_right
    refine ⟨parent, ⟨hp_mem, h_nesting⟩, ?_⟩
    intro q hq
    exact h_parent_unique q hq.1
/-! ## 8. Phase 1: Multi-level thinning (coarsest to finest) -/

/--
Process levels `0` through `j` (coarsest to finest), applying
`single_level_popularity_refine` at each level.

Returns a thinned shading `Z_out` and trapezoids `T_out` for levels `0..j`
with length lower bound, provenance, and coverage.

Active endpoints are NOT guaranteed in `Z_out` — they are active in the
shading at the time their level was processed, but later (finer-level)
thinning may remove them.  Use Phase 2 (`reanchor_trapezoids_on_shading`)
to re-anchor on the final shading.
-/
lemma phase1_thinning_up_to
    {N : ℕ} {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Z : Kakeya.Streamlined.TubeShading F}
    {rawTrapezoids : Fin N → Finset WZ1VerticalTrapezoid}
    {A_max : ENNReal}
    {L : Fin N → ℝ}
    (hL_pos : ∀ j, 0 ≤ L j)
    (h_slab_bound : ∀ (a b : ℝ), a ≤ b →
      volume (Z.union ∩ horizontalSlab a b) ≤ A_max * ENNReal.ofReal (b - a)) :
    ∀ (j : ℕ), j < N →
      ∀ (Z_j : Kakeya.Streamlined.TubeShading F),
        IsSubshading Z_j Z →
    ∃ (Z_out : Kakeya.Streamlined.TubeShading F)
      (T_out : Fin N → Finset WZ1VerticalTrapezoid),
      IsSubshading Z_out Z_j ∧
      (∀ (i : Fin N), (i : ℕ) ≤ j →
        (∀ t ∈ T_out i, L i ≤ t.length) ∧
        (∀ t ∈ T_out i,
          ∃ t0 ∈ rawTrapezoids i,
            t.core ⊆ t0.core ∧ t.slope = t0.slope ∧ t.intercept = t0.intercept ∧ t.height = t0.height)) ∧
      (∀ (i : Fin N), (i : ℕ) ≤ j →
        ∀ (z : ℝ), horizontalSlice Z_out.union z ≠ ∅ →
          ∃ t ∈ T_out i, z ∈ t.core) := by
  intro j
  induction j with
  | zero =>
    intro hj Z_j hZ_j_sub
    let j_fin : Fin N := ⟨0, hj⟩
    have h_slab_bound_j : ∀ (a b : ℝ), a ≤ b →
        volume (Z_j.union ∩ horizontalSlab a b) ≤ A_max * ENNReal.ofReal (b - a) := by
      intro a b hab
      have h1 : Z_j.union ∩ horizontalSlab a b ⊆ Z.union ∩ horizontalSlab a b :=
        Set.inter_subset_inter_left _ hZ_j_sub.union_subset
      exact (measure_mono h1).trans (h_slab_bound a b hab)
    rcases @single_level_popularity_refine delta F Z_j (rawTrapezoids j_fin) A_max (L j_fin)
        (hL_pos j_fin) h_slab_bound_j with
      ⟨Z_out, T_0, hZ_out_sub, h_active_0, h_len_0, h_prov_0, h_cov_0, h_same_0⟩
    let T_out : Fin N → Finset WZ1VerticalTrapezoid :=
      fun i => if (i : ℕ) = 0 then T_0 else ∅
    refine ⟨Z_out, T_out, hZ_out_sub, ?_⟩
    constructor
    · intro i hi
      have h_i_zero : (i : ℕ) = 0 := by omega
      have hT : T_out i = T_0 := by
        dsimp only [T_out]; rw [if_pos h_i_zero]
      have h_i_eq : i = j_fin := by apply Fin.ext; exact h_i_zero
      rw [hT, h_i_eq]; exact ⟨h_len_0, h_prov_0⟩
    · intro i hi z hz
      have h_i_zero : (i : ℕ) = 0 := by omega
      have hT : T_out i = T_0 := by
        dsimp only [T_out]; rw [if_pos h_i_zero]
      rw [hT]; exact h_cov_0 z hz
  | succ j' ih =>
    intro hj Z_j hZ_j_sub
    have h_j'_lt_N : j' < N := by omega
    rcases ih h_j'_lt_N Z_j hZ_j_sub with
      ⟨Z_prev, T_prev, hZ_prev_sub, h_props_prev, h_cov_prev⟩
    let j_fin : Fin N := ⟨j'.succ, hj⟩
    have h_slab_bound_prev : ∀ (a b : ℝ), a ≤ b →
        volume (Z_prev.union ∩ horizontalSlab a b) ≤ A_max * ENNReal.ofReal (b - a) := by
      intro a b hab
      let h_trans : IsSubshading Z_prev Z := fun i => Set.Subset.trans (hZ_prev_sub i) (hZ_j_sub i)
      have h1 : Z_prev.union ∩ horizontalSlab a b ⊆ Z.union ∩ horizontalSlab a b :=
        Set.inter_subset_inter_left _ h_trans.union_subset
      exact (measure_mono h1).trans (h_slab_bound a b hab)
    rcases @single_level_popularity_refine delta F Z_prev (rawTrapezoids j_fin) A_max (L j_fin)
        (hL_pos j_fin) h_slab_bound_prev with
      ⟨Z_out, T_j, hZ_out_sub, _, h_len_j, h_prov_j, h_cov_j, _⟩
    let T_out : Fin N → Finset WZ1VerticalTrapezoid :=
      fun i => if (i : ℕ) = j'.succ then T_j else T_prev i
    refine ⟨Z_out, T_out, fun i => Set.Subset.trans (hZ_out_sub i) (hZ_prev_sub i), ?_⟩
    constructor
    · intro i hi
      by_cases h_i_j : (i : ℕ) = j'.succ
      · have hT : T_out i = T_j := by
          dsimp only [T_out]; rw [if_pos h_i_j]
        have h_i_eq : i = j_fin := by apply Fin.ext; exact h_i_j
        rw [hT, h_i_eq]; exact ⟨h_len_j, h_prov_j⟩
      · have h_i_le : (i : ℕ) ≤ j' := by omega
        have h_ne : (i : ℕ) ≠ j'.succ := h_i_j
        have hT : T_out i = T_prev i := by
          dsimp only [T_out]; rw [if_neg h_ne]
        rw [hT]; exact h_props_prev i h_i_le
    · intro i hi z hz
      by_cases h_i_j : (i : ℕ) = j'.succ
      · have hT : T_out i = T_j := by
          dsimp only [T_out]; rw [if_pos h_i_j]
        rw [hT]; exact h_cov_j z hz
      · have h_i_le : (i : ℕ) ≤ j' := by omega
        have h_ne : (i : ℕ) ≠ j'.succ := h_i_j
        have hT : T_out i = T_prev i := by
          dsimp only [T_out]; rw [if_neg h_ne]
        rw [hT]
        have h_z_prev : horizontalSlice Z_prev.union z ≠ ∅ := by
          have h2 : Z_out.union ⊆ Z_prev.union := hZ_out_sub.union_subset
          have h3 : horizontalSlice Z_out.union z ⊆ horizontalSlice Z_prev.union z :=
            fun p hp => ⟨h2 hp.1, hp.2⟩
          exact Set.Nonempty.mono h3 (Set.nonempty_iff_ne_empty.mpr hz) |>.ne_empty
        exact h_cov_prev i h_i_le z h_z_prev

/--
Phase 1 top-level: process all `N` levels coarsest to finest.

Outputs `Z'` (thinned shading) and `T` (popular trapezoids at each level)
with length, provenance, and coverage.  Active endpoints not guaranteed.
-/
lemma phase1_thinning
    {N : ℕ} {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Z : Kakeya.Streamlined.TubeShading F}
    {rawTrapezoids : Fin N → Finset WZ1VerticalTrapezoid}
    {A_max : ENNReal}
    {L : Fin N → ℝ}
    (hN_pos : 0 < N)
    (hL_pos : ∀ j, 0 ≤ L j)
    (h_slab_bound : ∀ (a b : ℝ), a ≤ b →
      volume (Z.union ∩ horizontalSlab a b) ≤ A_max * ENNReal.ofReal (b - a)) :
    ∃ (Z' : Kakeya.Streamlined.TubeShading F)
      (T : Fin N → Finset WZ1VerticalTrapezoid),
      IsSubshading Z' Z ∧
      (∀ j, ∀ t ∈ T j, L j ≤ t.length) ∧
      (∀ j, ∀ t ∈ T j,
        ∃ t0 ∈ rawTrapezoids j,
          t.core ⊆ t0.core ∧ t.slope = t0.slope ∧ t.intercept = t0.intercept ∧ t.height = t0.height) ∧
      (∀ j, ∀ z, horizontalSlice Z'.union z ≠ ∅ → ∃ t ∈ T j, z ∈ t.core) := by
  have h_last_lt : N - 1 < N := by omega
  have h_id : IsSubshading Z Z := fun i => Set.Subset.refl (Z.carrier i)
  rcases phase1_thinning_up_to hL_pos h_slab_bound (N - 1) h_last_lt Z h_id with
    ⟨Z', T, hZ'_sub, h_props, h_cov⟩
  refine ⟨Z', T, hZ'_sub, ?_⟩
  constructor
  · intro j
    have hj_le : (j : ℕ) ≤ N - 1 := by omega
    exact (h_props j hj_le).1
  · constructor
    · intro j
      have hj_le : (j : ℕ) ≤ N - 1 := by omega
      exact (h_props j hj_le).2
    · intro j z hz
      have hj_le : (j : ℕ) ≤ N - 1 := by omega
      exact h_cov j hj_le z hz

/-! ## 9. Phase 2: Re-anchor trapezoids on final shading -/

/--
Re-anchor a finset of trapezoids on a shading `Z'`.

Given that every `t ∈ T` has `volumeInCore Z' t > A_max * ENNReal.ofReal L`,
find active endpoints within each core and shrink the trapezoid.

Outputs `T'` with:
- Active endpoints in `Z'`
- Length lower bound `L`
- Provenance (core subset, same slope and height)
- Every original trapezoid has a re-anchored counterpart

NOTE: This does NOT thin `Z'`.  Coverage with the shrunk cores requires a
separate argument or further thinning.
-/
lemma reanchor_trapezoids_on_shading
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Z' : Kakeya.Streamlined.TubeShading F}
    {T : Finset WZ1VerticalTrapezoid}
    {A_max : ENNReal} {L : ℝ}
    (hL_pos : 0 ≤ L)
    (h_slab_bound : ∀ (a b : ℝ), a ≤ b →
      volume (Z'.union ∩ horizontalSlab a b) ≤ A_max * ENNReal.ofReal (b - a))
    (h_vol : ∀ t ∈ T, volumeInCore Z' t > A_max * ENNReal.ofReal L) :
    ∃ (shrunk : WZ1VerticalTrapezoid → WZ1VerticalTrapezoid)
      (T' : Finset WZ1VerticalTrapezoid),
      (∀ t ∈ T, (shrunk t).core ⊆ t.core ∧
        (shrunk t).slope = t.slope ∧ (shrunk t).intercept = t.intercept ∧
        (shrunk t).height = t.height ∧ L ≤ (shrunk t).length) ∧
      (∀ t ∈ T, shrunk t ∈ T') ∧
      (∀ t' ∈ T', ∃ t ∈ T, t' = shrunk t) ∧
      (∀ t' ∈ T', horizontalSlice Z'.union t'.left ≠ ∅ ∧
                        horizontalSlice Z'.union t'.right ≠ ∅) ∧
      (∀ t' ∈ T', L ≤ t'.length) ∧
      (∀ t' ∈ T', ∃ t ∈ T,
        t'.core ⊆ t.core ∧ t'.slope = t.slope ∧ t'.intercept = t.intercept ∧ t'.height = t.height) := by
  classical
  let P (t : WZ1VerticalTrapezoid) : Prop :=
    ∃ (a b : ℝ), a ∈ activeSet Z' ∩ t.core ∧
      b ∈ activeSet Z' ∩ t.core ∧ b - a > L
  have h_main : ∀ t ∈ T, P t := by
    intro t ht
    exact active_points_from_volume hL_pos (h_vol t ht) h_slab_bound
  choose a b ha hb hdiff using h_main
  let shrunk (t : WZ1VerticalTrapezoid) : WZ1VerticalTrapezoid :=
    if ht : t ∈ T then
      shrinkTrapezoidToPoints t (a t ht) (b t ht)
        (by linarith [hdiff t ht]) (ha t ht).2 (hb t ht).2
    else t
  let T' : Finset WZ1VerticalTrapezoid := T.image shrunk
  have h_shrunk_spec : ∀ (t : WZ1VerticalTrapezoid) (ht : t ∈ T),
      (shrunk t).left = a t ht ∧ (shrunk t).right = b t ht ∧
      (shrunk t).core ⊆ t.core ∧ (shrunk t).slope = t.slope ∧
      (shrunk t).intercept = t.intercept ∧
      (shrunk t).height = t.height ∧ L ≤ (shrunk t).length := by
    intro t ht
    dsimp only [shrunk]
    rw [dif_pos ht]
    have h_spec := shrinkTrapezoidToPoints_spec t (a t ht) (b t ht)
      (by linarith [hdiff t ht]) (ha t ht).2 (hb t ht).2
    have h_len : L ≤ (b t ht) - (a t ht) := le_of_lt (hdiff t ht)
    exact ⟨h_spec.2.1, h_spec.2.2.1, h_spec.1, h_spec.2.2.2.1, h_spec.2.2.2.2.1, h_spec.2.2.2.2.2, h_len⟩
  have h_active : ∀ t' ∈ T',
      horizontalSlice Z'.union t'.left ≠ ∅ ∧
      horizontalSlice Z'.union t'.right ≠ ∅ := by
    intro t' ht'
    rcases Finset.mem_image.mp ht' with ⟨t, ht, rfl⟩
    have h_spec := h_shrunk_spec t ht
    have h_left_eq : (shrunk t).left = a t ht := h_spec.1
    have h_right_eq : (shrunk t).right = b t ht := h_spec.2.1
    constructor
    · rw [h_left_eq]; exact (ha t ht).1
    · rw [h_right_eq]; exact (hb t ht).1
  have h_length : ∀ t' ∈ T', L ≤ t'.length := by
    intro t' ht'
    rcases Finset.mem_image.mp ht' with ⟨t, ht, rfl⟩
    exact (h_shrunk_spec t ht).2.2.2.2.2.2
  have h_provenance : ∀ t' ∈ T', ∃ t ∈ T,
      t'.core ⊆ t.core ∧ t'.slope = t.slope ∧ t'.intercept = t.intercept ∧ t'.height = t.height := by
    intro t' ht'
    rcases Finset.mem_image.mp ht' with ⟨t, ht, rfl⟩
    have h_spec := h_shrunk_spec t ht
    exact ⟨t, ht, h_spec.2.2.1, h_spec.2.2.2.1, h_spec.2.2.2.2.1, h_spec.2.2.2.2.2.1⟩
  have h_counterpart : ∀ t ∈ T, ∃ t' ∈ T', t'.core ⊆ t.core := by
    intro t ht
    have h_st_in_T' : shrunk t ∈ T' := Finset.mem_image_of_mem shrunk ht
    have h_spec := h_shrunk_spec t ht
    exact ⟨shrunk t, h_st_in_T', h_spec.2.2.1⟩
  have h_shrunk_in_T' : ∀ t ∈ T, shrunk t ∈ T' := by
    intro t ht
    exact Finset.mem_image_of_mem shrunk ht
  have h_preimage : ∀ t' ∈ T', ∃ t ∈ T, t' = shrunk t := by
    intro t' ht'
    rcases Finset.mem_image.mp ht' with ⟨t, ht, rfl⟩
    exact ⟨t, ht, rfl⟩
  have h_shrunk_props : ∀ t ∈ T, (shrunk t).core ⊆ t.core ∧
      (shrunk t).slope = t.slope ∧ (shrunk t).intercept = t.intercept ∧
      (shrunk t).height = t.height ∧ L ≤ (shrunk t).length := by
    intro t ht
    have h_spec := h_shrunk_spec t ht
    exact ⟨h_spec.2.2.1, h_spec.2.2.2.1, h_spec.2.2.2.2.1, h_spec.2.2.2.2.2.1, h_spec.2.2.2.2.2.2⟩
  exact ⟨shrunk, T', h_shrunk_props, h_shrunk_in_T', h_preimage, h_active, h_length, h_provenance⟩

/-! ## 10. Second thinning: retain heights covered by all levels -/

/--
Thin a shading Z₁ to retain only heights that lie in at least one trapezoid core
at every hierarchy level.

Let `C_j := ⋃_{t ∈ T' j} t.core`.  We retain heights in `⋂_j C_j` and remove
the complement.  This ensures every retained height is covered at every level.

Endpoint survival: if an endpoint `z` (e.g. `t.left` or `t.right`) belongs to
`⋂_j C_j`, then no point at height `z` is removed, so its slice in the new
shading equals its slice in Z₁.
-/
lemma thin_to_intersection_of_cores
    {N : ℕ} {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    (Z₁ : Kakeya.Streamlined.TubeShading F)
    (T' : Fin N → Finset WZ1VerticalTrapezoid) :
    ∃ (Z'' : Kakeya.Streamlined.TubeShading F),
      IsSubshading Z'' Z₁ ∧
      (∀ (j : Fin N) (z : ℝ), horizontalSlice Z''.union z ≠ ∅ →
        ∃ t ∈ T' j, z ∈ t.core) ∧
      (∀ (z : ℝ), (∀ (j : Fin N), ∃ t ∈ T' j, z ∈ t.core) →
        horizontalSlice Z''.union z = horizontalSlice Z₁.union z) := by
  let coreUnion (j : Fin N) : Set ℝ := ⋃ t ∈ T' j, t.core
  let allCores : Set ℝ := {z | ∀ (j : Fin N), z ∈ coreUnion j}
  have h_allCores_meas : MeasurableSet allCores := by
    have h1 : ∀ (j : Fin N), MeasurableSet (coreUnion j) := by
      intro j
      apply MeasurableSet.biUnion (Set.to_countable _)
      intro t _
      exact measurableSet_Icc
    have h2 : allCores = ⋂ (j : Fin N), coreUnion j := by
      ext z
      simp [allCores, coreUnion]
      <;> tauto
    rw [h2]
    exact MeasurableSet.iInter fun j => h1 j
  let H : Set ℝ := allCoresᶜ
  have hH_meas : MeasurableSet H := h_allCores_meas.compl
  let Z'' : Kakeya.Streamlined.TubeShading F := thinShading Z₁ H hH_meas
  have hZ''_sub : IsSubshading Z'' Z₁ := thinShading_subshading
  have hZ''_union : Z''.union = Z₁.union \ {p : Point3 | p 2 ∈ H} := thinShading_union
  have h_coverage : ∀ (j : Fin N) (z : ℝ), horizontalSlice Z''.union z ≠ ∅ →
      ∃ t ∈ T' j, z ∈ t.core := by
    intro j z hz
    have h_z_notin_H : z ∉ H := by
      by_contra h
      have h4 : horizontalSlice Z''.union z = ∅ := by
        ext p
        simp only [horizontalSlice, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨h_in, h_eq⟩
        rw [hZ''_union] at h_in
        have h5 : p 2 ∉ H := h_in.2
        have h6 : p 2 ∈ H := by rw [h_eq]; exact h
        exact h5 h6
      rw [h4] at hz
      exact hz rfl
    have h_z_in_allCores : z ∈ allCores := by simpa [H] using h_z_notin_H
    have h5 : z ∈ coreUnion j := h_z_in_allCores j
    simpa [coreUnion] using h5
  have h_endpoint_survival : ∀ (z : ℝ), (∀ (j : Fin N), ∃ t ∈ T' j, z ∈ t.core) →
      horizontalSlice Z''.union z = horizontalSlice Z₁.union z := by
    intro z hz
    have h_z_in_allCores : z ∈ allCores := by
      have h' : ∀ (j : Fin N), z ∈ coreUnion j := by
        intro j
        simpa [coreUnion] using hz j
      simpa [allCores] using h'
    have h_z_notin_H : z ∉ H := by simpa [H] using h_z_in_allCores
    ext p
    simp only [horizontalSlice, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h_in, h_eq⟩
      rw [hZ''_union] at h_in
      exact ⟨h_in.1, h_eq⟩
    · rintro ⟨h_in, h_eq⟩
      have h7 : p 2 ∉ H := by rw [h_eq]; exact h_z_notin_H
      rw [hZ''_union]
      exact ⟨⟨h_in, h7⟩, h_eq⟩
  exact ⟨Z'', hZ''_sub, h_coverage, h_endpoint_survival⟩
lemma reanchor_with_coverage
    {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    {Z : Kakeya.Streamlined.TubeShading F}
    {T : Finset WZ1VerticalTrapezoid}
    {A_max : ENNReal} {L : ℝ}
    (hL_pos : 0 ≤ L)
    (hZ_compact : IsCompact Z.union)
    (h_slab_bound : ∀ (a b : ℝ), a ≤ b →
      volume (Z.union ∩ horizontalSlab a b) ≤ A_max * ENNReal.ofReal (b - a))
    (h_vol : ∀ t ∈ T, volumeInCore Z t > A_max * ENNReal.ofReal L) :
    ∃ (shrunk : WZ1VerticalTrapezoid → WZ1VerticalTrapezoid)
      (T' : Finset WZ1VerticalTrapezoid),
      (∀ t ∈ T, (shrunk t).core ⊆ t.core ∧
        (shrunk t).slope = t.slope ∧ (shrunk t).intercept = t.intercept ∧
        (shrunk t).height = t.height ∧ L ≤ (shrunk t).length) ∧
      (∀ t ∈ T, shrunk t ∈ T') ∧
      (∀ t' ∈ T', ∃ t ∈ T, t' = shrunk t) ∧
      (∀ t' ∈ T', horizontalSlice Z.union t'.left ≠ ∅ ∧
                        horizontalSlice Z.union t'.right ≠ ∅) ∧
      (∀ t' ∈ T', L ≤ t'.length) ∧
      (∀ t' ∈ T', ∃ t ∈ T,
        t'.core ⊆ t.core ∧ t'.slope = t.slope ∧ t'.intercept = t.intercept ∧ t'.height = t.height) ∧
      (∀ (z : ℝ), horizontalSlice Z.union z ≠ ∅ →
        (∃ t ∈ T, z ∈ t.core) → (∃ t' ∈ T', z ∈ t'.core)) := by
  classical
  have h_proj_cont : Continuous (fun p : Point3 => p 2) :=
    PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 2
  have h_active_eq : activeSet Z = (fun p : Point3 => p 2) '' Z.union := by
    ext z
    simp only [activeSet, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · intro h
      have hne : (horizontalSlice Z.union z).Nonempty := Set.nonempty_iff_ne_empty.mpr h
      rcases hne with ⟨p, hp⟩
      exact ⟨p, hp.1, hp.2⟩
    · rintro ⟨p, hp, rfl⟩
      have h : p ∈ horizontalSlice Z.union (p 2) := ⟨hp, rfl⟩
      exact Set.nonempty_iff_ne_empty.mp ⟨p, h⟩
  have h_active_compact : IsCompact (activeSet Z) :=
    h_active_eq.symm ▸ hZ_compact.image h_proj_cont
  let A (t : WZ1VerticalTrapezoid) : Set ℝ := activeSet Z ∩ t.core
  have hA_compact : ∀ t ∈ T, IsCompact (A t) := by
    intro t ht
    have h_core_compact : IsCompact (t.core) := isCompact_Icc
    exact h_active_compact.inter h_core_compact
  have hA_nonempty : ∀ t ∈ T, (A t).Nonempty := by
    intro t ht
    have h_main : ∃ (a b : ℝ), a ∈ A t ∧ b ∈ A t ∧ b - a > L :=
      active_points_from_volume hL_pos (h_vol t ht) h_slab_bound
    rcases h_main with ⟨a, b, ha, _, _⟩
    exact ⟨a, ha⟩
  let minA (t : WZ1VerticalTrapezoid) (ht : t ∈ T) : ℝ := sInf (A t)
  let maxA (t : WZ1VerticalTrapezoid) (ht : t ∈ T) : ℝ := sSup (A t)
  have hmin_in : ∀ t ht, minA t ht ∈ A t := fun t ht =>
    (hA_compact t ht).sInf_mem (hA_nonempty t ht)
  have hmax_in : ∀ t ht, maxA t ht ∈ A t := fun t ht =>
    (hA_compact t ht).sSup_mem (hA_nonempty t ht)
  have hA_bdd_below : ∀ t ht, BddBelow (A t) := fun t ht =>
    (hA_compact t ht).bddBelow
  have hA_bdd_above : ∀ t ht, BddAbove (A t) := fun t ht =>
    (hA_compact t ht).bddAbove
  have hmin_le : ∀ t ht x, x ∈ A t → minA t ht ≤ x := fun t ht x hx =>
    csInf_le (hA_bdd_below t ht) hx
  have hle_max : ∀ t ht x, x ∈ A t → x ≤ maxA t ht := fun t ht x hx =>
    le_csSup (hA_bdd_above t ht) hx
  have h_diff : ∀ t ht, maxA t ht - minA t ht > L := by
    intro t ht
    have h_main : ∃ (a b : ℝ), a ∈ A t ∧ b ∈ A t ∧ b - a > L :=
      active_points_from_volume hL_pos (h_vol t ht) h_slab_bound
    rcases h_main with ⟨a, b, ha, hb, hdiff⟩
    have h3 : minA t ht ≤ a := hmin_le t ht a ha
    have h4 : b ≤ maxA t ht := hle_max t ht b hb
    linarith
  let shrunk (t : WZ1VerticalTrapezoid) : WZ1VerticalTrapezoid :=
    if ht : t ∈ T then
      { left := minA t ht, right := maxA t ht,
        left_lt_right := by linarith [h_diff t ht],
        slope := t.slope, intercept := t.intercept,
        height := t.height, height_pos := t.height_pos }
    else t
  let T' : Finset WZ1VerticalTrapezoid := T.image shrunk
  have h_shrunk_spec : ∀ (t : WZ1VerticalTrapezoid) (ht : t ∈ T),
      (shrunk t).left = minA t ht ∧
      (shrunk t).right = maxA t ht ∧
      (shrunk t).slope = t.slope ∧
      (shrunk t).intercept = t.intercept ∧
      (shrunk t).height = t.height := by
    intro t ht
    have h_eq : shrunk t =
        { left := minA t ht, right := maxA t ht,
          left_lt_right := by linarith [h_diff t ht],
          slope := t.slope, intercept := t.intercept,
          height := t.height, height_pos := t.height_pos } := by
      dsimp only [shrunk]; rw [dif_pos ht]
    rw [h_eq] <;> simp
  refine ⟨shrunk, T', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Properties of shrunk trapezoids
    intro t ht
    have hs := h_shrunk_spec t ht
    constructor
    · -- core subset
      have h_left_in : minA t ht ∈ t.core := (hmin_in t ht).2
      have h_right_in : maxA t ht ∈ t.core := (hmax_in t ht).2
      have h_core_eq : (shrunk t).core = Set.Icc (minA t ht) (maxA t ht) := by
        simp [WZ1VerticalTrapezoid.core, hs.1, hs.2.1]
      rw [h_core_eq]
      exact Icc_subset_Icc h_left_in.1 h_right_in.2
    · exact ⟨hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2, by
        have h_len : (shrunk t).length = maxA t ht - minA t ht := by
          simp [WZ1VerticalTrapezoid.length, hs.1, hs.2.1]
        rw [h_len]
        exact le_of_lt (h_diff t ht)⟩
  · -- shrunk t ∈ T'
    intro t ht
    exact Finset.mem_image.mpr ⟨t, ht, rfl⟩
  · -- preimage
    intro t' ht'
    rcases Finset.mem_image.mp ht' with ⟨t, ht, rfl⟩
    exact ⟨t, ht, rfl⟩
  · -- active endpoints
    intro t' ht'
    rcases Finset.mem_image.mp ht' with ⟨t, ht, rfl⟩
    have hs := h_shrunk_spec t ht
    have h_left_active : (shrunk t).left ∈ activeSet Z := by
      rw [hs.1]; exact (hmin_in t ht).1
    have h_right_active : (shrunk t).right ∈ activeSet Z := by
      rw [hs.2.1]; exact (hmax_in t ht).1
    have h_left_ne : horizontalSlice Z.union (shrunk t).left ≠ ∅ := by
      simpa [activeSet] using h_left_active
    have h_right_ne : horizontalSlice Z.union (shrunk t).right ≠ ∅ := by
      simpa [activeSet] using h_right_active
    exact ⟨h_left_ne, h_right_ne⟩
  · -- length bound
    intro t' ht'
    rcases Finset.mem_image.mp ht' with ⟨t, ht, rfl⟩
    have hs := h_shrunk_spec t ht
    have h_len : (shrunk t).length = maxA t ht - minA t ht := by
      simp [WZ1VerticalTrapezoid.length, hs.1, hs.2.1]
    rw [h_len]
    exact le_of_lt (h_diff t ht)
  · -- provenance
    intro t' ht'
    rcases Finset.mem_image.mp ht' with ⟨t, ht, rfl⟩
    have hs := h_shrunk_spec t ht
    refine ⟨t, ht, ?_⟩
    have h_left_in : minA t ht ∈ t.core := (hmin_in t ht).2
    have h_right_in : maxA t ht ∈ t.core := (hmax_in t ht).2
    constructor
    · have h_core_eq : (shrunk t).core = Set.Icc (minA t ht) (maxA t ht) := by
        simp [WZ1VerticalTrapezoid.core, hs.1, hs.2.1]
      rw [h_core_eq]
      exact Icc_subset_Icc h_left_in.1 h_right_in.2
    · exact ⟨hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2⟩
  · -- coverage preservation
    intro z hz_active h_cover
    rcases h_cover with ⟨t, ht, hz_core⟩
    have hz_active' : z ∈ activeSet Z := by simpa [activeSet] using hz_active
    have hz_in_A : z ∈ A t := ⟨hz_active', hz_core⟩
    have h1 : minA t ht ≤ z := hmin_le t ht z hz_in_A
    have h2 : z ≤ maxA t ht := hle_max t ht z hz_in_A
    refine ⟨shrunk t, Finset.mem_image.mpr ⟨t, ht, rfl⟩, ?_⟩
    have hs := h_shrunk_spec t ht
    have h_core_eq : (shrunk t).core = Set.Icc (minA t ht) (maxA t ht) := by
      simp [WZ1VerticalTrapezoid.core, hs.1, hs.2.1]
    rw [h_core_eq]
    exact ⟨h1, h2⟩

/-! ## 6. Compact subshading with arbitrary error -/

/--
Inner-regularize every carrier of a finite shading, removing at most `ε`
volume from each carrier.  The resulting carriers are compact, so the
shading union is compact.

The total removed union volume is at most `F.card * ε`.
-/
lemma compact_subshading_with_eps
    {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    {Y : Kakeya.Streamlined.TubeShading F}
    (ε : ENNReal) (hε : ε ≠ 0) :
    ∃ (Z : Kakeya.Streamlined.TubeShading F),
      IsSubshading Z Y ∧
      (∀ i, IsCompact (Z.carrier i)) ∧
      (∀ i, MeasureTheory.volume (Y.carrier i \ Z.carrier i) < ε) := by
  have h_main : ∀ i : Fin F.card, ∃ (K : Set Point3),
      K ⊆ Y.carrier i ∧ IsCompact K ∧
        MeasureTheory.volume (Y.carrier i \ K) < ε := by
    intro i
    set A : Set Point3 := Y.carrier i with hA_def
    have hA_meas : MeasurableSet A := Y.measurable_carrier i
    have hA_sub : A ⊆ (F.tube i).carrier := Y.subset_body i
    have h_tube_compact : IsCompact (F.tube i).carrier := by
      have h_seg_compact : IsCompact (unitSegment (F.tube i).base (F.tube i).direction) := by
        exact isCompact_Icc.image
          (continuous_const.add (continuous_id.smul continuous_const))
      simpa [DeltaTube.carrier] using h_seg_compact.cthickening
    have hA_lt_top : MeasureTheory.volume A < ⊤ :=
      (measure_mono hA_sub).trans_lt h_tube_compact.measure_lt_top
    have hA_ne_top : MeasureTheory.volume A ≠ ⊤ := hA_lt_top.ne
    by_cases h0 : MeasureTheory.volume A = 0
    · have h_pos : (0 : ENNReal) < ε :=
        zero_lt_iff.mpr hε
      refine ⟨∅, by simp, isCompact_empty, ?_⟩
      rw [Set.diff_empty]
      rw [h0]
      exact h_pos
    · rcases hA_meas.exists_isCompact_isClosed_sdiff_lt hA_ne_top hε with
        ⟨K, hK_sub, hK_compact, _, hK_sdiff⟩
      exact ⟨K, hK_sub, hK_compact, hK_sdiff⟩
  choose K hK_sub hK_compact hK_sdiff using h_main
  let Z : Kakeya.Streamlined.TubeShading F :=
    { carrier := K
      measurable_carrier := fun i => (hK_compact i).measurableSet
      subset_body := fun i => (hK_sub i).trans (Y.subset_body i) }
  refine ⟨Z, fun i => hK_sub i, fun i => hK_compact i, fun i => hK_sdiff i⟩

/-! ## Compact subshading with volume, mass, and per-core retention -/

noncomputable section CompactSubshading

open MeasureTheory Set Finset ENNReal

/-- Given `a > b` finite ENNReals, produce a positive real gap such that `a > b + ofReal gap`. -/
lemma ennreal_gap {a b : ENNReal} (ha : a ≠ ⊤) (hb : b ≠ ⊤) (h : a > b) :
    ∃ (gap : ℝ), 0 < gap ∧ a > b + ENNReal.ofReal gap := by
  let gap : ℝ := (a.toReal - b.toReal) / 2
  have h1 : a.toReal > b.toReal := ENNReal.toReal_lt_toReal hb ha |>.mpr h
  have hgap_pos : 0 < gap := by dsimp only [gap]; linarith
  have h_a_eq : ENNReal.ofReal a.toReal = a := by rw [ENNReal.ofReal_toReal ha]
  have h_b_eq : ENNReal.ofReal b.toReal = b := by rw [ENNReal.ofReal_toReal hb]
  have h2 : a.toReal > b.toReal + gap := by dsimp only [gap]; linarith
  have h_b_nonneg : 0 ≤ b.toReal := by positivity
  have h_gap_nonneg : 0 ≤ gap := by linarith
  have h_sum_nonneg : 0 ≤ b.toReal + gap := by linarith
  have h3 : ENNReal.ofReal (b.toReal + gap) < ENNReal.ofReal a.toReal := by
    rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg h_sum_nonneg]
    exact h2
  have h6 : ENNReal.ofReal (b.toReal + gap) = ENNReal.ofReal b.toReal + ENNReal.ofReal gap := by
    rw [ENNReal.ofReal_add h_b_nonneg h_gap_nonneg]
  rw [h_a_eq, h6, h_b_eq] at h3
  exact ⟨gap, hgap_pos, h3⟩

/-- If `a = c + loss` and `loss < ofReal gap` and `a > b + ofReal gap`, then `c > b`. -/
lemma ennreal_retention {a b c loss : ENNReal} {gap : ℝ}
    (h_eq : a = c + loss) (h_loss : loss < ENNReal.ofReal gap)
    (h_orig : a > b + ENNReal.ofReal gap) (h_gap_lt_top : ENNReal.ofReal gap ≠ ⊤) : c > b := by
  rw [h_eq] at h_orig
  have h5 : c + ENNReal.ofReal gap ≥ c + loss := by
    exact add_le_add_right (le_of_lt h_loss) c
  have h6 : c + ENNReal.ofReal gap > b + ENNReal.ofReal gap :=
    lt_of_lt_of_le h_orig h5
  exact (ENNReal.add_lt_add_iff_right h_gap_lt_top).mp h6

/-- Sum of strict inequalities over nonempty finset in ENNReal, when all values are finite. -/
lemma finset_sum_strict_lt {α : Type*} {s : Finset α} (hs : s.Nonempty)
    {f g : α → ENNReal} (hfg : ∀ i ∈ s, f i < g i) (hg_top : ∀ i ∈ s, g i ≠ ⊤) :
    ∑ i ∈ s, f i < ∑ i ∈ s, g i := by
  have hf_top : ∀ i ∈ s, f i ≠ ⊤ := by
    intro i hi
    have h : f i < g i := hfg i hi
    exact ne_top_of_lt h
  have h1 : (∑ i ∈ s, (f i).toReal) < (∑ i ∈ s, (g i).toReal) := by
    apply Finset.sum_lt_sum_of_nonempty hs
    intro i hi
    have hfi : f i < g i := hfg i hi
    exact (ENNReal.toReal_lt_toReal (hf_top i hi) (hg_top i hi)).mpr hfi
  have h2 : (∑ i ∈ s, f i).toReal = ∑ i ∈ s, (f i).toReal := by
    rw [ENNReal.toReal_sum] <;> intro i _; exact hf_top i ‹_›
  have h3 : (∑ i ∈ s, g i).toReal = ∑ i ∈ s, (g i).toReal := by
    rw [ENNReal.toReal_sum] <;> intro i _; exact hg_top i ‹_›
  have h4g : (∑ i ∈ s, g i) ≠ ⊤ := by
    rw [ENNReal.sum_ne_top]; exact hg_top
  have h4f : (∑ i ∈ s, f i) ≠ ⊤ := by
    rw [ENNReal.sum_ne_top]; exact hf_top
  have h5 : (∑ i ∈ s, f i).toReal < (∑ i ∈ s, g i).toReal := by
    calc (∑ i ∈ s, f i).toReal = ∑ i ∈ s, (f i).toReal := h2
    _ < ∑ i ∈ s, (g i).toReal := h1
    _ = (∑ i ∈ s, g i).toReal := h3.symm
  exact (ENNReal.toReal_lt_toReal h4f h4g).mp h5

/--
Main construction: given positive gaps, build a compact subshading retaining
per-core volume, total union volume, and mass.
-/
lemma compact_subshading_main
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Z : Kakeya.Streamlined.TubeShading F}
    {T : Finset WZ1VerticalTrapezoid}
    {core_bound : WZ1VerticalTrapezoid → ENNReal} {vol_bound mass_bound : ENNReal}
    (hZ_ball : Z.union ⊆ Metric.closedBall (0 : Point3) 1)
    (hF_card_pos : 0 < F.card)
    (hZ_vol_lt_top : volume Z.union ≠ ⊤)
    (hZ_mass_lt_top : Z.mass ≠ ⊤)
    (min_gap vol_gap mass_gap : ℝ)
    (hmin_gap_pos : 0 < min_gap)
    (h_min_gap_le_vol : min_gap ≤ vol_gap)
    (h_min_gap_le_mass : min_gap ≤ mass_gap)
    (hvol_gap_works : volume Z.union > vol_bound + ENNReal.ofReal vol_gap)
    (hmass_gap_works : Z.mass > mass_bound + ENNReal.ofReal mass_gap)
    (h_core_data : ∀ t ∈ T, ∃ (g : ℝ), 0 < g ∧
      volumeInCore Z t > core_bound t + ENNReal.ofReal g ∧ min_gap ≤ g) :
    ∃ (Z_comp : Kakeya.Streamlined.TubeShading F),
      IsSubshading Z_comp Z ∧
      IsCompact Z_comp.union ∧
      (∀ t ∈ T, volumeInCore Z_comp t > core_bound t) ∧
      volume Z_comp.union ≥ vol_bound ∧
      Z_comp.mass ≥ mass_bound := by
  classical
  let n : ℕ := F.toBodyFamily.card
  have hn_pos : 0 < n := by
    dsimp only [n]
    exact hF_card_pos
  let eps_real : ℝ := min_gap / (n : ℝ)
  have heps_real_pos : 0 < eps_real := by
    dsimp only [eps_real]; apply div_pos hmin_gap_pos; exact_mod_cast hn_pos
  let eps : ENNReal := ENNReal.ofReal eps_real
  have heps_pos : 0 < eps := ENNReal.ofReal_pos.mpr heps_real_pos
  have heps_ne_zero : eps ≠ 0 := heps_pos.ne'
  have heps_lt_top : eps ≠ ⊤ := by simp [eps]
  have h_total : (n : ENNReal) * eps = ENNReal.ofReal min_gap := by
    have h1 : (n : ENNReal) * eps = ENNReal.ofReal ((n : ℝ) * eps_real) := by
      have h2 : ENNReal.ofReal ((n : ℝ) * eps_real) =
          ENNReal.ofReal (n : ℝ) * ENNReal.ofReal eps_real := by
        rw [ENNReal.ofReal_mul] <;> positivity
      rw [h2]
      have h3 : ENNReal.ofReal (n : ℝ) = (n : ENNReal) := by simp
      rw [h3] <;> rfl
    rw [h1]
    have h4 : (n : ℝ) * eps_real = min_gap := by
      dsimp only [eps_real]; field_simp [hn_pos.ne'] <;> ring
    rw [h4]
  have h_main : ∀ (i : Fin n), ∃ (K : Set Point3),
      K ⊆ Z.carrier i ∧ IsCompact K ∧ volume (Z.carrier i \ K) < eps := by
    intro i
    have h_meas : MeasurableSet (Z.carrier i) := Z.measurable_carrier i
    have h1 : Z.carrier i ⊆ Z.union := by intro x hx; exact ⟨i, hx⟩
    have h_fin : volume (Z.carrier i) ≠ ⊤ := ne_top_of_le_ne_top hZ_vol_lt_top (measure_mono h1)
    rcases h_meas.exists_isCompact_lt_add h_fin heps_ne_zero with ⟨K, hK_sub, hK_compact, h_vol_lt⟩
    have hK_meas : MeasurableSet K := hK_compact.measurableSet
    have hDiff_meas : MeasurableSet (Z.carrier i \ K) := h_meas.diff hK_meas
    have h_union_eq : K ∪ (Z.carrier i \ K) = Z.carrier i := by
      ext x; simp [hK_sub] <;> tauto
    have h_disj : Disjoint K (Z.carrier i \ K) := by
      rw [Set.disjoint_left]; intro x hx1 hx2; exact hx2.2 hx1
    have h10 : volume (K ∪ (Z.carrier i \ K)) = volume K + volume (Z.carrier i \ K) :=
      measure_union h_disj hDiff_meas
    have h_eq : volume (Z.carrier i) = volume K + volume (Z.carrier i \ K) := by
      have h11 : volume (K ∪ (Z.carrier i \ K)) = volume (Z.carrier i) := by rw [h_union_eq]
      rw [← h11]
      exact h10
    have hK_lt_top : volume K ≠ ⊤ := ne_top_of_le_ne_top h_fin (measure_mono hK_sub)
    have h_loss_lt : volume (Z.carrier i \ K) < eps := by
      have h_vol_lt2 : volume K + volume (Z.carrier i \ K) < volume K + eps := by
        rw [h_eq] at h_vol_lt; exact h_vol_lt
      exact (ENNReal.add_lt_add_iff_left hK_lt_top).mp h_vol_lt2
    exact ⟨K, hK_sub, hK_compact, h_loss_lt⟩
  choose K hK_sub hK_compact hK_loss using h_main
  let Z_comp : Kakeya.Streamlined.TubeShading F :=
    { carrier := K
      measurable_carrier := fun i => (hK_compact i).measurableSet
      subset_body := fun i => Set.Subset.trans (hK_sub i) (Z.subset_body i) }
  have hZ_comp_sub : IsSubshading Z_comp Z := fun i => hK_sub i
  have h_union_compact : IsCompact Z_comp.union := by
    have h_eq : Z_comp.union = ⋃ i : Fin n, K i := by
      ext x; simp [Kakeya.Streamlined.Shading.union, Z_comp] <;> aesop
    rw [h_eq]; exact isCompact_iUnion (fun i => hK_compact i)
  have h_nonempty : (Finset.univ : Finset (Fin n)).Nonempty := by
    exact ⟨⟨0, hn_pos⟩, by simp⟩
  have h_loss_sum : ∑ i : Fin n, volume (Z.carrier i \ K i) < (n : ENNReal) * eps := by
    have h4 : ∑ i : Fin n, volume (Z.carrier i \ K i) < ∑ i : Fin n, eps :=
      finset_sum_strict_lt h_nonempty (fun i _ => hK_loss i) (fun i _ => heps_lt_top)
    have h5 : ∑ i : Fin n, eps = (n : ENNReal) * eps := by
      simp [Finset.sum_const] <;> ring
    rw [h5] at h4; exact h4
  have h_diff_subset : Z.union \ Z_comp.union ⊆ ⋃ i : Fin n, (Z.carrier i \ K i) := by
    intro x hx
    rcases hx.1 with ⟨i, hi⟩
    have hxi : x ∉ K i := by
      intro h
      have h_in_union : x ∈ Z_comp.union := by
        simp only [Kakeya.Streamlined.Shading.union, Set.mem_setOf_eq]
        exact ⟨i, h⟩
      exact hx.2 h_in_union
    exact Set.mem_iUnion.mpr ⟨i, ⟨hi, hxi⟩⟩
  have h_vol_loss : volume (Z.union \ Z_comp.union) < (n : ENNReal) * eps := by
    calc volume (Z.union \ Z_comp.union)
      ≤ volume (⋃ i : Fin n, (Z.carrier i \ K i)) := measure_mono h_diff_subset
    _ ≤ ∑ i : Fin n, volume (Z.carrier i \ K i) := by
      simpa [tsum_fintype] using measure_iUnion_le (fun i : Fin n => Z.carrier i \ K i)
    _ < (n : ENNReal) * eps := h_loss_sum
  have hZ_union_meas : MeasurableSet Z.union := by
    have h : Z.union = ⋃ i : Fin n, Z.carrier i := by
      ext x; simp [Kakeya.Streamlined.Shading.union] <;> aesop
    rw [h]; exact MeasurableSet.iUnion (fun i => Z.measurable_carrier i)
  have hZ_comp_union_meas : MeasurableSet Z_comp.union := h_union_compact.measurableSet
  have h_diff_meas : MeasurableSet (Z.union \ Z_comp.union) := hZ_union_meas.diff hZ_comp_union_meas
  have h_vol_decomp : volume Z.union = volume Z_comp.union + volume (Z.union \ Z_comp.union) := by
    have h_sub : Z_comp.union ⊆ Z.union := hZ_comp_sub.union_subset
    have h_disj : Disjoint Z_comp.union (Z.union \ Z_comp.union) := by
      rw [Set.disjoint_left]; intro x hx1 hx2; exact hx2.2 hx1
    have h_eq : Z.union = Z_comp.union ∪ (Z.union \ Z_comp.union) := by
      ext x
      simp only [Set.mem_union, Set.mem_diff]
      constructor
      · intro hx
        by_cases h : x ∈ Z_comp.union
        · exact Or.inl h
        · exact Or.inr ⟨hx, h⟩
      · rintro (h | ⟨h, _⟩)
        · exact h_sub h
        · exact h
    have h_measure : volume (Z_comp.union ∪ (Z.union \ Z_comp.union)) =
        volume Z_comp.union + volume (Z.union \ Z_comp.union) :=
      measure_union h_disj h_diff_meas
    have h_vol : volume Z.union = volume (Z_comp.union ∪ (Z.union \ Z_comp.union)) :=
      congr_arg volume h_eq
    rw [h_vol, h_measure]
  have h_mass_decomp : Z.mass = Z_comp.mass + ∑ i : Fin n, volume (Z.carrier i \ K i) := by
    simp [Kakeya.Streamlined.Shading.mass]
    have h : ∀ (i : Fin n), volume (Z.carrier i) = volume (K i) + volume (Z.carrier i \ K i) := by
      intro i
      have hK_meas : MeasurableSet (K i) := (hK_compact i).measurableSet
      have hDiff_meas : MeasurableSet (Z.carrier i \ K i) := (Z.measurable_carrier i).diff hK_meas
      have h_union_eq : K i ∪ (Z.carrier i \ K i) = Z.carrier i := by
        ext x; simp [hK_sub i] <;> tauto
      have h_disj : Disjoint (K i) (Z.carrier i \ K i) := by
        rw [Set.disjoint_left]; intro x hx1 hx2; exact hx2.2 hx1
      have h_vol : volume (K i ∪ (Z.carrier i \ K i)) = volume (K i) + volume (Z.carrier i \ K i) :=
        measure_union h_disj hDiff_meas
      rw [← h_vol, h_union_eq]
    rw [Finset.sum_congr rfl (fun i _ => h i), Finset.sum_add_distrib] <;> ring
  have h_core_ret : ∀ t ∈ T, volumeInCore Z_comp t > core_bound t := by
    intro t ht
    rcases h_core_data t ht with ⟨g, hg_pos, hg_works, h_min_le_g⟩
    let loss_t := volume ((Z.union \ Z_comp.union) ∩ horizontalSlab t.left t.right)
    have h_loss_t_lt : loss_t < ENNReal.ofReal min_gap := by
      calc loss_t
        ≤ volume (Z.union \ Z_comp.union) := measure_mono (fun x hx => hx.1)
      _ < (n : ENNReal) * eps := h_vol_loss
      _ = ENNReal.ofReal min_gap := h_total
    have h_loss_lt_gap : loss_t < ENNReal.ofReal g := by
      calc loss_t < ENNReal.ofReal min_gap := h_loss_t_lt
           _ ≤ ENNReal.ofReal g := ENNReal.ofReal_le_ofReal h_min_le_g
    have h_slab_meas : MeasurableSet (horizontalSlab t.left t.right) :=
      measurableSet_horizontalSlab t.left t.right
    have h_part2_meas : MeasurableSet ((Z.union \ Z_comp.union) ∩ horizontalSlab t.left t.right) :=
      h_diff_meas.inter h_slab_meas
    have h_decomp : volumeInCore Z t = volumeInCore Z_comp t + loss_t := by
      have h1 : Z.union ∩ horizontalSlab t.left t.right =
          (Z_comp.union ∩ horizontalSlab t.left t.right) ∪
          ((Z.union \ Z_comp.union) ∩ horizontalSlab t.left t.right) := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_diff]
        constructor
        · rintro ⟨hZ, hslab⟩
          by_cases h : x ∈ Z_comp.union
          · exact Or.inl ⟨h, hslab⟩
          · exact Or.inr ⟨⟨hZ, h⟩, hslab⟩
        · rintro (⟨hZcomp, hslab⟩ | ⟨⟨hZ, _⟩, hslab⟩)
          · exact ⟨hZ_comp_sub.union_subset hZcomp, hslab⟩
          · exact ⟨hZ, hslab⟩
      have h_disj : Disjoint (Z_comp.union ∩ horizontalSlab t.left t.right)
          ((Z.union \ Z_comp.union) ∩ horizontalSlab t.left t.right) := by
        rw [Set.disjoint_left]
        intro x hx1 hx2
        have h_in : x ∈ Z_comp.union := hx1.1
        have h_notin : x ∉ Z_comp.union := hx2.1.2
        exact h_notin h_in
      have h_goal : volume (Z.union ∩ horizontalSlab t.left t.right) =
          volume (Z_comp.union ∩ horizontalSlab t.left t.right) + loss_t := by
        rw [h1, measure_union h_disj h_part2_meas] <;> rfl
      have h_set_eq1 : Z.union ∩ horizontalSlab t.left t.right =
          Z.union ∩ {p : Point3 | p 2 ∈ Set.Icc t.left t.right} := by
        ext x; simp [horizontalSlab] <;> rfl
      have h_set_eq2 : Z_comp.union ∩ horizontalSlab t.left t.right =
          Z_comp.union ∩ {p : Point3 | p 2 ∈ Set.Icc t.left t.right} := by
        ext x; simp [horizontalSlab] <;> rfl
      rw [h_set_eq1, h_set_eq2] at h_goal
      simpa [volumeInCore, volumeInSlab] using h_goal
    exact ennreal_retention h_decomp h_loss_lt_gap hg_works (by simp)
  have h_vol_ret : volume Z_comp.union ≥ vol_bound := by
    have h_loss_lt_gap : volume (Z.union \ Z_comp.union) < ENNReal.ofReal vol_gap := by
      calc volume (Z.union \ Z_comp.union) < (n : ENNReal) * eps := h_vol_loss
           _ = ENNReal.ofReal min_gap := h_total
           _ ≤ ENNReal.ofReal vol_gap := ENNReal.ofReal_le_ofReal h_min_gap_le_vol
    exact le_of_lt (ennreal_retention h_vol_decomp h_loss_lt_gap hvol_gap_works (by simp))
  have h_mass_loss_lt : ∑ i : Fin n, volume (Z.carrier i \ K i) < ENNReal.ofReal mass_gap := by
    calc ∑ i : Fin n, volume (Z.carrier i \ K i) < (n : ENNReal) * eps := h_loss_sum
         _ = ENNReal.ofReal min_gap := h_total
         _ ≤ ENNReal.ofReal mass_gap := ENNReal.ofReal_le_ofReal h_min_gap_le_mass
  have h_mass_ret : Z_comp.mass ≥ mass_bound := by
    exact le_of_lt (ennreal_retention h_mass_decomp h_mass_loss_lt hmass_gap_works (by simp))
  exact ⟨Z_comp, hZ_comp_sub, h_union_compact, h_core_ret, h_vol_ret, h_mass_ret⟩

/--
Construct a compact subshading Z_comp of Z retaining per-core volume,
total union volume, and mass above specified lower bounds.
-/
lemma compact_subshading_with_full_retention
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Z : Kakeya.Streamlined.TubeShading F}
    {T : Finset WZ1VerticalTrapezoid}
    {core_bound : WZ1VerticalTrapezoid → ENNReal} {vol_bound mass_bound : ENNReal}
    (hZ_ball : Z.union ⊆ Metric.closedBall (0 : Point3) 1)
    (hF_card_pos : 0 < F.card)
    (h_vol : ∀ t ∈ T, volumeInCore Z t > core_bound t)
    (h_vol_bound : volume Z.union > vol_bound)
    (h_mass_bound : Z.mass > mass_bound)
    (h_core_bound_lt_top : ∀ t ∈ T, core_bound t ≠ ⊤)
    (h_vol_bound_lt_top : vol_bound ≠ ⊤)
    (h_mass_bound_lt_top : mass_bound ≠ ⊤) :
    ∃ (Z_comp : Kakeya.Streamlined.TubeShading F),
      IsSubshading Z_comp Z ∧
      IsCompact Z_comp.union ∧
      (∀ t ∈ T, volumeInCore Z_comp t > core_bound t) ∧
      volume Z_comp.union ≥ vol_bound ∧
      Z_comp.mass ≥ mass_bound := by
  classical
  let n : ℕ := F.toBodyFamily.card
  have h_ball_lt_top : volume (Metric.closedBall (0 : Point3) 1) ≠ ⊤ :=
    (IsCompact.measure_lt_top (isCompact_closedBall 0 1)).ne
  have hZ_vol_lt_top : volume Z.union ≠ ⊤ := ne_top_of_le_ne_top h_ball_lt_top (measure_mono hZ_ball)
  have hZ_mass_lt_top : Z.mass ≠ ⊤ := by
    have h : Z.mass = ∑ i : Fin n, volume (Z.carrier i) := by rfl
    rw [h]
    rw [ENNReal.sum_ne_top]
    intro i _
    have h1 : Z.carrier i ⊆ Z.union := by intro x hx; exact ⟨i, hx⟩
    exact ne_top_of_le_ne_top hZ_vol_lt_top (measure_mono h1)
  have h_core_vol_lt_top : ∀ t ∈ T, volumeInCore Z t ≠ ⊤ := by
    intro t _
    have h1 : (Z.union ∩ horizontalSlab t.left t.right) ⊆ Z.union := fun x hx => hx.1
    exact ne_top_of_le_ne_top hZ_vol_lt_top (measure_mono h1)
  rcases ennreal_gap hZ_vol_lt_top h_vol_bound_lt_top h_vol_bound with ⟨vol_gap, hvol_gap_pos, hvol_gap_works⟩
  rcases ennreal_gap hZ_mass_lt_top h_mass_bound_lt_top h_mass_bound with ⟨mass_gap, hmass_gap_pos, hmass_gap_works⟩
  have h_core_gaps : ∀ t ∈ T, ∃ (g : ℝ), 0 < g ∧ volumeInCore Z t > core_bound t + ENNReal.ofReal g := by
    intro t ht
    exact ennreal_gap (h_core_vol_lt_top t ht) (h_core_bound_lt_top t ht) (h_vol t ht)
  choose core_gap hcore_gap_pos hcore_gap_works using h_core_gaps
  by_cases hT_empty : T = ∅
  · let min_gap : ℝ := min vol_gap mass_gap
    have hmin_gap_pos : 0 < min_gap := lt_min hvol_gap_pos hmass_gap_pos
    exact compact_subshading_main hZ_ball hF_card_pos hZ_vol_lt_top hZ_mass_lt_top
      min_gap vol_gap mass_gap hmin_gap_pos
      (min_le_left _ _) (min_le_right _ _)
      hvol_gap_works hmass_gap_works
      (fun t ht => by rw [hT_empty] at ht; simp at ht)
  · have hT_nonempty : T.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]; exact hT_empty
    let core_gap_total : WZ1VerticalTrapezoid → ℝ := fun t =>
      if h : t ∈ T then core_gap t h else 0
    rcases Finset.exists_min_image T core_gap_total hT_nonempty with ⟨t0, ht0, h_min_core⟩
    let min_core_gap : ℝ := core_gap_total t0
    have hmin_core_gap_pos : 0 < min_core_gap := by
      dsimp only [min_core_gap, core_gap_total]
      rw [dif_pos ht0]
      exact hcore_gap_pos t0 ht0
    let min_gap : ℝ := min min_core_gap (min vol_gap mass_gap)
    have hmin_gap_pos : 0 < min_gap := by
      apply lt_min hmin_core_gap_pos
      apply lt_min hvol_gap_pos hmass_gap_pos
    have h_min_gap_le_core : ∀ (t) (ht : t ∈ T), min_gap ≤ core_gap t ht := by
      intro t ht
      have h_total_eq : core_gap_total t = core_gap t ht := by
        dsimp only [core_gap_total]; rw [dif_pos ht]
      calc min_gap ≤ min_core_gap := min_le_left _ _
           _ = core_gap_total t0 := by rfl
           _ ≤ core_gap_total t := h_min_core t ht
           _ = core_gap t ht := h_total_eq
    have h_min_gap_le_vol : min_gap ≤ vol_gap := by
      calc min_gap ≤ min vol_gap mass_gap := min_le_right _ _
           _ ≤ vol_gap := min_le_left _ _
    have h_min_gap_le_mass : min_gap ≤ mass_gap := by
      calc min_gap ≤ min vol_gap mass_gap := min_le_right _ _
           _ ≤ mass_gap := min_le_right _ _
    have h_core_data : ∀ t ∈ T, ∃ (g : ℝ), 0 < g ∧
        volumeInCore Z t > core_bound t + ENNReal.ofReal g ∧ min_gap ≤ g := by
      intro t ht
      exact ⟨core_gap t ht, hcore_gap_pos t ht, hcore_gap_works t ht, h_min_gap_le_core t ht⟩
    exact compact_subshading_main hZ_ball hF_card_pos hZ_vol_lt_top hZ_mass_lt_top
      min_gap vol_gap mass_gap hmin_gap_pos
      h_min_gap_le_vol h_min_gap_le_mass
      hvol_gap_works hmass_gap_works h_core_data

end CompactSubshading

end Kakeya.Assouad

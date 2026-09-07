import MyLeanRepo.Kakeya.AssertionD
import MyLeanRepo.Kakeya.Assouad.TubeVolumeScaling
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Tube axial slab volume bound

For a δ-tube T and axial interval [a,b], the volume of
T ∩ π_T⁻¹([a,b]) is at most 4δ²(b-a).

Proof: rigidly transform T to the canonical tube along e0, then
the slab intersection is contained in [a,b] × [-δ,δ] × [-δ,δ],
whose volume is (b-a) * (2δ) * (2δ) = 4δ²(b-a).
-/

noncomputable section

open MeasureTheory Metric Set

namespace Kakeya.Assouad

/-- Volume bound for axial slab of a tube. -/
lemma tube_slab_volume_bound {δ : ℝ} (hδ : 0 < δ)
    (T : Kakeya.DeltaTube δ) (a b : ℝ) (hab : a ≤ b) :
    volume (T.carrier ∩ {x : Point3 | a ≤ inner ℝ (x - T.base) T.direction ∧
        inner ℝ (x - T.base) T.direction ≤ b}) ≤
    ENNReal.ofReal (4 * δ^2 * (b - a)) := by
  let e0 : Point3 := EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
  have he0 : ‖e0‖ = 1 := by simp [e0]
  have hnorm : ‖T.direction‖ = ‖e0‖ := by
    rw [T.direction_unit, he0]
  let A : Point3 ≃ₗᵢ[ℝ] Point3 :=
    Submodule.reflection (ℝ ∙ (T.direction - e0))ᗮ
  have hA_dir : A T.direction = e0 := Submodule.reflection_sub hnorm
  let translate : Point3 ≃ᵢ Point3 :=
    { toFun := fun x => x - T.base
      invFun := fun y => y + T.base
      left_inv := by intro x; simp
      right_inv := by intro y; simp
      isometry_toFun := by
        intro x y
        simp [edist_dist, dist_eq_norm] }
  let rigid : Point3 ≃ᵢ Point3 := translate.trans A
  have hrigid : ∀ x, rigid x = A (x - T.base) := by intro x; rfl
  have hA_preserving : MeasurePreserving A volume volume := A.measurePreserving
  have htranslate_preserving : MeasurePreserving translate volume volume :=
    measurePreserving_sub_right volume T.base
  have hpreserving : MeasurePreserving rigid volume volume :=
    hA_preserving.comp htranslate_preserving
  have hinner_e0 : ∀ (y : Point3), inner ℝ y e0 = y 0 := by
    intro y
    have h1 : inner ℝ y e0 = ∑ i : Fin 3, inner ℝ (y i) (e0 i) := PiLp.inner_apply y e0
    rw [h1]
    have h2 : ∑ i : Fin 3, inner ℝ (y i) (e0 i) = ∑ i : Fin 3, (y i) * (e0 i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Real.inner_apply]
    rw [h2]
    simp [e0, Fin.sum_univ_succ]
    <;> ring
  have hproj : ∀ (x : Point3), inner ℝ (x - T.base) T.direction = (rigid x) 0 := by
    intro x
    have h1 : inner ℝ (x - T.base) T.direction = inner ℝ (A (x - T.base)) (A T.direction) := by
      rw [A.inner_map_map]
    rw [h1, hA_dir, hinner_e0]
    <;> rfl
  have hsegment : rigid '' Kakeya.unitSegment T.base T.direction = Kakeya.unitSegment 0 e0 := by
    ext y
    simp only [Kakeya.unitSegment, Set.mem_image]
    constructor
    · rintro ⟨x, ⟨t, ht, rfl⟩, rfl⟩
      refine ⟨t, ht, ?_⟩
      simp [hrigid, hA_dir, A.map_smul]
    · rintro ⟨t, ht, rfl⟩
      refine ⟨T.base + t • T.direction, ⟨t, ht, rfl⟩, ?_⟩
      simp [hrigid, hA_dir, A.map_smul]
  let canonicalTube : Set Point3 := Metric.cthickening δ (Kakeya.unitSegment 0 e0)
  have hcarrier : rigid '' T.carrier = canonicalTube := by
    have hcthick : ∀ (e : Point3 ≃ᵢ Point3), e '' Metric.cthickening δ (Kakeya.unitSegment T.base T.direction) =
        Metric.cthickening δ (e '' Kakeya.unitSegment T.base T.direction) := by
      intro e
      ext z
      simp only [Metric.mem_cthickening_iff, Set.mem_image]
      constructor
      · rintro ⟨x, hx, rfl⟩
        rw [Metric.infEDist_image e.isometry]
        exact hx
      · intro hz
        refine ⟨e.symm z, ?_, e.apply_symm_apply z⟩
        have himage : e.symm '' (e '' Kakeya.unitSegment T.base T.direction) = Kakeya.unitSegment T.base T.direction := by
          rw [← Set.image_comp] <;> simp
        have hdist := Metric.infEDist_image e.symm.isometry (x := z) (t := e '' Kakeya.unitSegment T.base T.direction)
        rw [himage] at hdist
        rw [hdist]
        exact hz
    rw [Kakeya.DeltaTube.carrier, hcthick rigid, hsegment]
  have hcoord0_cont : Continuous (fun (y : Point3) => y 0) := by
    fun_prop
  let slab1 : Set Point3 := {y | a ≤ y 0}
  let slab2 : Set Point3 := {y | y 0 ≤ b}
  let slab : Set Point3 := slab1 ∩ slab2
  have hslab_meas : MeasurableSet slab := by
    have h1 : MeasurableSet slab1 := by
      exact measurableSet_le measurable_const hcoord0_cont.measurable
    have h2 : MeasurableSet slab2 := by
      exact measurableSet_le hcoord0_cont.measurable measurable_const
    exact h1.inter h2
  let S_orig : Set Point3 := T.carrier ∩ {x | a ≤ inner ℝ (x - T.base) T.direction ∧ inner ℝ (x - T.base) T.direction ≤ b}
  have himage : rigid '' S_orig = canonicalTube ∩ slab := by
    ext z
    simp only [Set.mem_image, Set.mem_inter_iff, S_orig]
    constructor
    · rintro ⟨x, ⟨hxT, hxproj⟩, rfl⟩
      have hzT : rigid x ∈ canonicalTube := by
        have h : rigid x ∈ rigid '' T.carrier := ⟨x, hxT, rfl⟩
        rw [hcarrier] at h
        exact h
      have hzproj : a ≤ (rigid x) 0 ∧ (rigid x) 0 ≤ b := by
        rw [←hproj x] <;> exact hxproj
      exact ⟨hzT, hzproj⟩
    · rintro ⟨hzT, hzproj⟩
      let x := rigid.symm z
      have h_eq : rigid x = z := rigid.apply_symm_apply z
      have hxT : x ∈ T.carrier := by
        have h : z ∈ canonicalTube := hzT
        rw [←hcarrier] at h
        rcases h with ⟨w, hw, rfl⟩
        have h2 : w = x := by
          exact rigid.symm_apply_apply w ▸ rfl
        rw [h2] at hw
        exact hw
      have hxproj : a ≤ inner ℝ (x - T.base) T.direction ∧ inner ℝ (x - T.base) T.direction ≤ b := by
        have h : inner ℝ (x - T.base) T.direction = (rigid x) 0 := hproj x
        rw [h, h_eq]
        exact hzproj
      exact ⟨x, ⟨hxT, hxproj⟩, h_eq⟩
  let rigidMeasurable : Point3 ≃ᵐ Point3 :=
    { toFun := rigid
      invFun := rigid.symm
      left_inv := rigid.left_inv
      right_inv := rigid.right_inv
      measurable_toFun := rigid.continuous.measurable
      measurable_invFun := rigid.symm.continuous.measurable }
  have hpreserving_symm : MeasurePreserving rigid.symm volume volume :=
    hpreserving.symm rigidMeasurable
  have hpreimage : rigid '' S_orig = rigid.symm ⁻¹' S_orig := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hz
      exact ⟨rigid.symm z, hz, rigid.apply_symm_apply z⟩
  have hvol : volume (rigid '' S_orig) = volume S_orig := by
    rw [hpreimage]
    exact MeasurePreserving.measure_preimage_equiv (f := rigidMeasurable.symm) hpreserving_symm S_orig
  let lo : Fin 3 → ℝ := fun i =>
    match i with
    | 0 => a
    | 1 => -δ
    | 2 => -δ
  let hi : Fin 3 → ℝ := fun i =>
    match i with
    | 0 => b
    | 1 => δ
    | 2 => δ
  have hlohi : ∀ i, lo i ≤ hi i := by
    intro i
    fin_cases i <;> dsimp [lo, hi] <;> linarith [hδ]
  have hcanonical_segment_compact : IsCompact (Kakeya.unitSegment 0 e0) := by
    apply IsCompact.image isCompact_Icc
    fun_prop
  have hbound : canonicalTube ∩ slab ⊆ (WithLp.toLp 2) '' Set.Icc lo hi := by
    intro y hy
    have h1 : y ∈ canonicalTube := hy.1
    have h2 : y ∈ slab := hy.2
    have h3 : ∃ (t : ℝ), t ∈ Set.Icc (0 : ℝ) 1 ∧ dist y (t • e0) ≤ δ := by
      have h4 : canonicalTube = ⋃ (z : Point3) (_ : z ∈ Kakeya.unitSegment 0 e0), Metric.closedBall z δ :=
        hcanonical_segment_compact.cthickening_eq_biUnion_closedBall hδ.le
      rw [h4] at h1
      rcases Set.mem_iUnion₂.mp h1 with ⟨z, hz, hzy⟩
      rcases hz with ⟨t, ht, rfl⟩
      exact ⟨t, ht, by simpa [Metric.mem_closedBall] using hzy⟩
    rcases h3 with ⟨t, ht, hdist⟩
    have h4 : ‖y - t • e0‖ ≤ δ := by simpa [dist_eq_norm] using hdist
    have h5 : ∀ (i : Fin 3), |(y - t • e0) i| ≤ δ := by
      intro i
      have h6 : |(y - t • e0) i| ≤ dist y (t • e0) := PiLp.dist_apply_le y (t • e0) i
      have h7 : dist y (t • e0) ≤ δ := hdist
      linarith
    have h7 : a ≤ y 0 ∧ y 0 ≤ b := h2
    have h_coord1 : (t • e0) 1 = 0 := by simp [e0]
    have h_coord2 : (t • e0) 2 = 0 := by simp [e0]
    have h8 : y.ofLp ∈ Set.Icc lo hi := by
      simp only [Set.mem_Icc, lo, hi]
      constructor
      · intro i
        fin_cases i
        · exact h7.1
        · have h9 : |y 1| ≤ δ := by
            simpa [h_coord1] using h5 1
          exact (abs_le.mp h9).1
        · have h9 : |y 2| ≤ δ := by
            simpa [h_coord2] using h5 2
          exact (abs_le.mp h9).1
      · intro i
        fin_cases i
        · exact h7.2
        · have h9 : |y 1| ≤ δ := by
            simpa [h_coord1] using h5 1
          exact (abs_le.mp h9).2
        · have h9 : |y 2| ≤ δ := by
            simpa [h_coord2] using h5 2
          exact (abs_le.mp h9).2
    exact ⟨y.ofLp, h8, by simp [WithLp.ofLp_toLp]⟩
  have hrectvol : volume ((WithLp.toLp 2) '' Set.Icc lo hi) =
      ENNReal.ofReal ((b - a) * (2 * δ) * (2 * δ)) := by
    rw [volume_rectBox lo hi hlohi]
    <;> simp [lo, hi] <;> ring
  rw [←hvol, himage]
  calc volume (canonicalTube ∩ slab)
    ≤ volume ((WithLp.toLp 2) '' Set.Icc lo hi) := measure_mono hbound
  _ = ENNReal.ofReal ((b - a) * (2 * δ) * (2 * δ)) := hrectvol
  _ = ENNReal.ofReal (4 * δ^2 * (b - a)) := by
    congr 1 <;> ring

/-- Volume bound for the endpoint caps of a tube: the portion of the tube
whose axial projection falls outside `[0,1]` has volume at most `8δ³`. -/
lemma tube_endcap_volume_bound {δ : ℝ} (hδ : 0 < δ) (hδ_le_one : δ ≤ 1)
    (T : Kakeya.DeltaTube δ) :
    volume (T.carrier \ {x : Point3 | (0 : ℝ) ≤ inner ℝ (x - T.base) T.direction ∧
                          inner ℝ (x - T.base) T.direction ≤ 1}) ≤
    ENNReal.ofReal (8 * δ^3) := by
  let π : Point3 → ℝ := fun x => inner ℝ (x - T.base) T.direction
  let middle : Set Point3 := {x | 0 ≤ π x ∧ π x ≤ 1}
  let leftCap : Set Point3 := T.carrier ∩ {x | π x < 0}
  let rightCap : Set Point3 := T.carrier ∩ {x | π x > 1}

  have hdecomp : T.carrier \ middle = leftCap ∪ rightCap := by
    ext x
    constructor
    · intro h
      have hxT : x ∈ T.carrier := h.1
      have hnm : x ∉ middle := h.2
      have hdef : π x < 0 ∨ π x > 1 := by
        by_cases h1 : π x < 0
        · exact Or.inl h1
        · have h2 : π x > 1 := by
            have h3 : 0 ≤ π x := by linarith
            exact by_contra fun h4 => hnm (by exact ⟨h3, by linarith⟩)
          exact Or.inr h2
      rcases hdef with (h1 | h2)
      · exact Or.inl ⟨hxT, h1⟩
      · exact Or.inr ⟨hxT, h2⟩
    · intro h
      rcases h with (hL | hR)
      · have hxT : x ∈ T.carrier := hL.1
        have h1 : π x < 0 := by simpa [Set.mem_setOf_eq] using hL.2
        exact ⟨hxT, fun hmid => by linarith [hmid.1, hmid.2]⟩
      · have hxT : x ∈ T.carrier := hR.1
        have h2 : π x > 1 := by simpa [Set.mem_setOf_eq] using hR.2
        exact ⟨hxT, fun hmid => by linarith [hmid.1, hmid.2]⟩

  -- Axial range: for x ∈ T.carrier, π(x) ∈ [-δ, 1+δ]
  have haxial : ∀ (x : Point3), x ∈ T.carrier → -δ ≤ π x ∧ π x ≤ 1 + δ := by
    intro x hx
    have hcompact : IsCompact (Kakeya.unitSegment T.base T.direction) := by
      apply IsCompact.image isCompact_Icc
      fun_prop
    have h4 : T.carrier = ⋃ (z : Point3) (_ : z ∈ Kakeya.unitSegment T.base T.direction),
        Metric.closedBall z δ :=
      hcompact.cthickening_eq_biUnion_closedBall hδ.le
    rw [h4] at hx
    rcases Set.mem_iUnion₂.mp hx with ⟨z, hz, hzy⟩
    rcases hz with ⟨t, ht, rfl⟩
    have hdist : dist x (T.base + t • T.direction) ≤ δ := by
      simpa [Metric.mem_closedBall] using hzy
    let y := x - (T.base + t • T.direction)
    have hynorm : ‖y‖ ≤ δ := by simpa [y, dist_eq_norm] using hdist
    have hpi : π x = inner ℝ y T.direction + t := by
      have h1 : x - T.base = y + t • T.direction := by
        simp [y] <;> abel
      have h2 : inner ℝ (x - T.base) T.direction =
          inner ℝ (y + t • T.direction) T.direction := by rw [h1]
      have h3 : inner ℝ (y + t • T.direction) T.direction =
          inner ℝ y T.direction + inner ℝ (t • T.direction) T.direction :=
        inner_add_left y (t • T.direction) T.direction
      have h4 : inner ℝ (t • T.direction) T.direction =
          t * inner ℝ T.direction T.direction := by
        simpa [inner_smul_left] using rfl
      have h5 : inner ℝ T.direction T.direction = ‖T.direction‖ ^ 2 :=
        real_inner_self_eq_norm_sq T.direction
      have h6 : ‖T.direction‖ ^ 2 = 1 := by
        rw [T.direction_unit] <;> norm_num
      simp only [π, h2, h3, h4, h5, h6] <;> ring
    have hcs : |inner ℝ y T.direction| ≤ ‖y‖ * ‖T.direction‖ :=
      abs_real_inner_le_norm y T.direction
    have hdir : ‖T.direction‖ = 1 := T.direction_unit
    have hbound1 : |inner ℝ y T.direction| ≤ δ := by
      rw [hdir] at hcs
      have h : ‖y‖ * (1 : ℝ) ≤ δ := by
        rw [mul_one] <;> exact hynorm
      exact hcs.trans h
    have hlower : -δ ≤ inner ℝ y T.direction := (abs_le.mp hbound1).1
    have hupper : inner ℝ y T.direction ≤ δ := (abs_le.mp hbound1).2
    rw [hpi]
    constructor <;> linarith [ht.1, ht.2]

  -- Left cap: {π < 0} ⊆ {-δ ≤ π ≤ 0}
  have hleft_sub : leftCap ⊆ T.carrier ∩ {x | -δ ≤ π x ∧ π x ≤ 0} := by
    intro x hx
    have hxT : x ∈ T.carrier := hx.1
    have hpi_neg : π x < 0 := hx.2
    have haxial' := haxial x hxT
    exact ⟨hxT, ⟨haxial'.1, by linarith⟩⟩
  have hleft_vol : volume leftCap ≤ ENNReal.ofReal (4 * δ^3) := by
    have h : volume leftCap ≤ ENNReal.ofReal (4 * δ^2 * (0 - (-δ))) :=
      (measure_mono hleft_sub).trans (tube_slab_volume_bound hδ T (-δ) 0 (by linarith))
    have h' : 4 * δ^2 * (0 - (-δ)) = 4 * δ^3 := by ring
    rw [h'] at h
    exact h

  -- Right cap: {π > 1} ⊆ {1 ≤ π ≤ 1+δ}
  have hright_sub : rightCap ⊆ T.carrier ∩ {x | 1 ≤ π x ∧ π x ≤ 1 + δ} := by
    intro x hx
    have hxT : x ∈ T.carrier := hx.1
    have hpi_gt : π x > 1 := hx.2
    have haxial' := haxial x hxT
    exact ⟨hxT, ⟨by linarith, haxial'.2⟩⟩
  have hright_vol : volume rightCap ≤ ENNReal.ofReal (4 * δ^3) := by
    have h : volume rightCap ≤ ENNReal.ofReal (4 * δ^2 * ((1 + δ) - 1)) :=
      (measure_mono hright_sub).trans (tube_slab_volume_bound hδ T 1 (1 + δ) (by linarith))
    have h' : 4 * δ^2 * ((1 + δ) - 1) = 4 * δ^3 := by ring
    rw [h'] at h
    exact h

  rw [hdecomp]
  have hunion : volume (leftCap ∪ rightCap) ≤ volume leftCap + volume rightCap :=
    measure_union_le _ _
  have hnonneg : 0 ≤ 4 * δ^3 := by positivity
  calc
    volume (leftCap ∪ rightCap)
      ≤ volume leftCap + volume rightCap := hunion
    _ ≤ ENNReal.ofReal (4 * δ^3) + ENNReal.ofReal (4 * δ^3) :=
      add_le_add hleft_vol hright_vol
    _ = ENNReal.ofReal (8 * δ^3) := by
      rw [← ENNReal.ofReal_add hnonneg hnonneg]
      <;> congr 1 <;> ring

end Kakeya.Assouad

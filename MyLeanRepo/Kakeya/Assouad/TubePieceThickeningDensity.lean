import MyLeanRepo.Kakeya.Assouad.EssentiallyDistinctCardBound
import MyLeanRepo.Kakeya.Assouad.TubeBallDensityRho
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.SelectedScaleStatements
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Tube-piece thickening density

The proof double-counts pairs `(x, y)` with `x` in the common shaded piece,
`y` in the coarse tube, and `dist x y ≤ rho`.  A coarse tube contains a
radius-`rho / 2` ball near every one of its points, while a radius-`rho` ball
cuts a fine tube in volume at most `2 * pi * delta^2 * rho`.
-/

noncomputable section

open MeasureTheory Metric Set

namespace Kakeya.Assouad

private def shiftedCylinder (r L a : ℝ) : Set Point3 :=
  {x | (x 1)^2 + (x 2)^2 ≤ r^2 ∧ a ≤ x 0 ∧ x 0 ≤ a + L}

private lemma volume_shiftedCylinder
    (r L a : ℝ) (hr : 0 ≤ r) (hL : 0 ≤ L) :
    volume (shiftedCylinder r L a) =
      ENNReal.ofReal (Real.pi * r^2 * L) := by
  let v : Point3 :=
    -a • EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
  have h1 :
      shiftedCylinder r L a =
        (fun x : Point3 => v + x) ⁻¹' (stdCylinder r L) := by
    ext x
    simp only [shiftedCylinder, stdCylinder, Set.mem_preimage,
      Set.mem_setOf_eq]
    constructor
    · rintro ⟨hrad, ha1, ha2⟩
      have h3 : (v + x) 1 = x 1 := by simp [v]
      have h4 : (v + x) 2 = x 2 := by simp [v]
      have h5 : (v + x) 0 = x 0 - a := by simp [v]; ring
      exact ⟨by rw [h3, h4]; exact hrad, by linarith, by linarith⟩
    · rintro ⟨hrad, h11, h12⟩
      have h3 : (v + x) 1 = x 1 := by simp [v]
      have h4 : (v + x) 2 = x 2 := by simp [v]
      have h5 : (v + x) 0 = x 0 - a := by simp [v]; ring
      exact
        ⟨by rw [← h3, ← h4]; exact hrad, by linarith, by linarith⟩
  rw [h1]
  have hmp :
      MeasurePreserving (fun x : Point3 => v + x) volume volume :=
    measurePreserving_add_left volume v
  have h_meas : MeasurableSet (stdCylinder r L) := by
    have h11 :
        Measurable (fun x : Point3 => (x 1)^2 + (x 2)^2) := by
      fun_prop
    have h21 : Measurable (fun x : Point3 => x 0) := by
      fun_prop
    have hrad :
        MeasurableSet {x : Point3 | (x 1)^2 + (x 2)^2 ≤ r^2} :=
      measurableSet_le h11 (by fun_prop)
    have haxial :
        MeasurableSet {x : Point3 | 0 ≤ x 0 ∧ x 0 ≤ L} :=
      h21 measurableSet_Icc
    exact hrad.inter haxial
  have h_eq1 := hmp.measure_preimage h_meas.nullMeasurableSet
  rw [h_eq1, volume_stdCylinder r L hr hL]

private def infiniteCylinder (r : ℝ) : Set Point3 :=
  {x | (x 1)^2 + (x 2)^2 ≤ r^2}

private lemma canonical_tube_subset_infiniteCylinder
    {r : ℝ} (hr : 0 < r) :
    Metric.cthickening r
        (Kakeya.unitSegment 0
          (EuclideanSpace.single (0 : Fin 3) (1 : ℝ))) ⊆
      infiniteCylinder r := by
  intro x hx
  have hcompact :
      IsCompact
        (Kakeya.unitSegment 0
          (EuclideanSpace.single (0 : Fin 3) (1 : ℝ))) := by
    apply IsCompact.image isCompact_Icc
    fun_prop
  rw [hcompact.cthickening_eq_biUnion_closedBall hr.le] at hx
  rcases Set.mem_iUnion₂.mp hx with ⟨y, hy, hxy⟩
  rcases hy with ⟨t, ht, rfl⟩
  let e0 : Point3 :=
    EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
  let p : Point3 := t • e0
  have hdist : dist x p ≤ r := by
    simpa [Metric.mem_closedBall] using hxy
  let z : Point3 := x - p
  have h_le : ‖z‖ ≤ r := by
    have h : dist x p = ‖z‖ := by rw [dist_eq_norm]
    rw [← h]
    exact hdist
  have h_norm_sq :
      ‖z‖ ^ 2 = ∑ i : Fin 3, (z i)^2 :=
    EuclideanSpace.real_norm_sq_eq z
  have h_sum :
      ∑ i : Fin 3, (z i)^2 =
        (z 0)^2 + (z 1)^2 + (z 2)^2 := by
    simp [Fin.sum_univ_succ]
    ring
  have h2 :
      ‖z‖ ^ 2 = (z 0)^2 + (z 1)^2 + (z 2)^2 := by
    rw [h_norm_sq, h_sum]
  have h' : ‖z‖ ^ 2 ≤ r^2 := by gcongr
  have h_all : (z 0)^2 + (z 1)^2 + (z 2)^2 ≤ r^2 := h2 ▸ h'
  have h_sq : (z 1)^2 + (z 2)^2 ≤ r^2 := by
    nlinarith [sq_nonneg (z 0)]
  have hp1 : p 1 = 0 := by simp [p, e0]
  have hp2 : p 2 = 0 := by simp [p, e0]
  have hz1 : z 1 = x 1 - p 1 := by rfl
  have hz2 : z 2 = x 2 - p 2 := by rfl
  rw [hz1, hz2] at h_sq
  rw [show x 1 - p 1 = x 1 by rw [hp1]; ring,
    show x 2 - p 2 = x 2 by rw [hp2]; ring] at h_sq
  exact h_sq

private lemma infiniteCylinder_ball_subset_shiftedCylinder
    {r R : ℝ} (y : Point3) :
    infiniteCylinder r ∩ Metric.closedBall y R ⊆
      shiftedCylinder r (2 * R) (y 0 - R) := by
  intro x hx
  have h1 : (x 1)^2 + (x 2)^2 ≤ r^2 := hx.1
  have h2 : dist x y ≤ R := hx.2
  have h3 : |x 0 - y 0| ≤ dist x y :=
    PiLp.dist_apply_le x y 0
  have h4 : |x 0 - y 0| ≤ R := h3.trans h2
  exact
    ⟨h1, by linarith [(abs_le.mp h4).1],
      by linarith [(abs_le.mp h4).2]⟩

private lemma IsometryEquiv.cthickening_image
    {α β : Type*} [PseudoEMetricSpace α] [PseudoEMetricSpace β]
    (e : α ≃ᵢ β) (delta : ℝ) (s : Set α) :
    e '' Metric.cthickening delta s =
      Metric.cthickening delta (e '' s) := by
  ext y
  simp only [Metric.mem_cthickening_iff, Set.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Metric.infEDist_image e.isometry]
    exact hx
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    have himage : e.symm '' (e '' s) = s := by
      rw [← Set.image_comp]
      simp
    have hdist :=
      Metric.infEDist_image e.symm.isometry
        (x := y) (t := e '' s)
    rw [himage] at hdist
    rw [hdist]
    exact hy

private def tubeRigid {delta : ℝ}
    (T : Kakeya.DeltaTube delta) : Point3 ≃ᵢ Point3 := by
  let e0 : Point3 :=
    EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
  let A : Point3 ≃ₗᵢ[ℝ] Point3 :=
    Submodule.reflection (ℝ ∙ (T.direction - e0))ᗮ
  let translate : Point3 ≃ᵢ Point3 :=
    { toFun := fun x => x - T.base
      invFun := fun y => y + T.base
      left_inv := by intro x; simp
      right_inv := by intro y; simp
      isometry_toFun := by
        intro x y
        simp [edist_dist, dist_eq_norm] }
  exact translate.trans A

private lemma tubeRigid_segment_image
    {delta : ℝ} (T : Kakeya.DeltaTube delta) :
    tubeRigid T '' Kakeya.unitSegment T.base T.direction =
      Kakeya.unitSegment 0
        (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) := by
  let e0 : Point3 :=
    EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
  let rigid := tubeRigid T
  let A : Point3 ≃ₗᵢ[ℝ] Point3 :=
    Submodule.reflection (ℝ ∙ (T.direction - e0))ᗮ
  have hrigid : ∀ z, rigid z = A (z - T.base) := by
    intro z
    rfl
  have hA : A T.direction = e0 := by
    have he0 : ‖e0‖ = 1 := by simp [e0]
    have hnorm : ‖T.direction‖ = ‖e0‖ := by
      rw [T.direction_unit, he0]
    exact Submodule.reflection_sub hnorm
  ext y
  simp only [Kakeya.unitSegment, Set.mem_image]
  constructor
  · rintro ⟨x, ⟨t, ht, rfl⟩, rfl⟩
    refine ⟨t, ht, ?_⟩
    have h_align : A (t • T.direction) = t • e0 := by
      rw [A.map_smul, hA] <;> simp
    have h :
        rigid (T.base + t • T.direction) = t • e0 := by
      rw [hrigid]
      have h2 :
          T.base + t • T.direction - T.base =
            t • T.direction := by
        abel
      rw [h2]
      exact h_align
    simpa [zero_add] using h.symm
  · rintro ⟨t, ht, rfl⟩
    refine
      ⟨T.base + t • T.direction, ⟨t, ht, rfl⟩, ?_⟩
    have h_align : A (t • T.direction) = t • e0 := by
      rw [A.map_smul, hA] <;> simp
    have h :
        rigid (T.base + t • T.direction) = t • e0 := by
      rw [hrigid]
      have h2 :
          T.base + t • T.direction - T.base =
            t • T.direction := by
        abel
      rw [h2]
      exact h_align
    simpa using h

private lemma tube_ball_intersection_volume
    {delta R : ℝ} (hdelta : 0 < delta) (hR : 0 < R)
    (T : Kakeya.DeltaTube delta) (x : Point3) :
    volume (T.carrier ∩ Metric.closedBall x R) ≤
      ENNReal.ofReal (Real.pi * delta^2 * 2 * R) := by
  let e0 : Point3 :=
    EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
  let rigid := tubeRigid T
  have hsegment :
      rigid '' Kakeya.unitSegment T.base T.direction =
        Kakeya.unitSegment 0 e0 :=
    tubeRigid_segment_image T
  have hcarrier :
      rigid '' T.carrier =
        Metric.cthickening delta (Kakeya.unitSegment 0 e0) := by
    rw [Kakeya.DeltaTube.carrier,
      IsometryEquiv.cthickening_image rigid delta, hsegment]
  have hpreserving :
      MeasurePreserving rigid volume volume := by
    let A : Point3 ≃ₗᵢ[ℝ] Point3 :=
      Submodule.reflection (ℝ ∙ (T.direction - e0))ᗮ
    have h1 : MeasurePreserving A volume volume :=
      A.measurePreserving
    have h2 :
        MeasurePreserving (fun x : Point3 => x - T.base) volume volume :=
      measurePreserving_sub_right volume T.base
    exact h1.comp h2
  let rigidMeasurable : Point3 ≃ᵐ Point3 :=
    { toFun := rigid
      invFun := rigid.symm
      left_inv := rigid.left_inv
      right_inv := rigid.right_inv
      measurable_toFun := rigid.continuous.measurable
      measurable_invFun := rigid.symm.continuous.measurable }
  have hpreserving_symm :
      MeasurePreserving rigid.symm volume volume :=
    hpreserving.symm rigidMeasurable
  let y : Point3 := rigid x
  have h_ball_image :
      rigid '' Metric.closedBall x R = Metric.closedBall y R :=
    rigid.image_closedBall x R
  have h_image_inter :
      rigid '' (T.carrier ∩ Metric.closedBall x R) =
        (rigid '' T.carrier) ∩
          (rigid '' Metric.closedBall x R) := by
    rw [Set.image_inter rigid.injective]
  have hpreimage :
      rigid '' (T.carrier ∩ Metric.closedBall x R) =
        rigid.symm ⁻¹' (T.carrier ∩ Metric.closedBall x R) := by
    ext z
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa using hw
    · intro hz
      exact ⟨rigid.symm z, hz, rigid.apply_symm_apply z⟩
  have hvol :
      volume (rigid '' (T.carrier ∩ Metric.closedBall x R)) =
        volume (T.carrier ∩ Metric.closedBall x R) := by
    rw [hpreimage]
    exact MeasurePreserving.measure_preimage_equiv
      (f := rigidMeasurable.symm) hpreserving_symm _
  have h_main :
      volume (rigid '' (T.carrier ∩ Metric.closedBall x R)) ≤
        ENNReal.ofReal (Real.pi * delta^2 * 2 * R) := by
    rw [h_image_inter, h_ball_image, hcarrier]
    let canonicalTube :=
      Metric.cthickening delta (Kakeya.unitSegment 0 e0)
    have h1 :
        canonicalTube ∩ Metric.closedBall y R ⊆
          infiniteCylinder delta ∩ Metric.closedBall y R :=
      Set.inter_subset_inter
        (canonical_tube_subset_infiniteCylinder hdelta)
        Set.Subset.rfl
    have h2 :
        infiniteCylinder delta ∩ Metric.closedBall y R ⊆
          shiftedCylinder delta (2 * R) (y 0 - R) :=
      infiniteCylinder_ball_subset_shiftedCylinder y
    have h3 :
        volume (canonicalTube ∩ Metric.closedBall y R) ≤
          volume (shiftedCylinder delta (2 * R) (y 0 - R)) :=
      measure_mono (h1.trans h2)
    have h4 :
        volume (shiftedCylinder delta (2 * R) (y 0 - R)) =
          ENNReal.ofReal (Real.pi * delta^2 * (2 * R)) :=
      volume_shiftedCylinder delta (2 * R) (y 0 - R)
        hdelta.le (by linarith)
    rw [h4] at h3
    convert h3 using 1 <;> ring_nf
  rw [← hvol]
  exact h_main

theorem tube_piece_thickening_density :
    TubePieceThickeningDensityStatement := by
  intro delta rho hdelta hdelta_rho hrho_one T S E
    hE_meas hE_T hE_S
  have hrho : 0 < rho := lt_of_lt_of_le hdelta hdelta_rho
  by_cases hE_empty : E = ∅
  · rw [hE_empty]
    simp [Kakeya.deltaTubeVolume]
    <;> aesop
  have hT_compact : IsCompact T.carrier := by
    have hseg :
        IsCompact (Kakeya.unitSegment T.base T.direction) := by
      apply IsCompact.image isCompact_Icc
      fun_prop
    exact hseg.cthickening
  have hS_compact : IsCompact S.carrier := by
    have hseg :
        IsCompact (Kakeya.unitSegment S.base S.direction) := by
      apply IsCompact.image isCompact_Icc
      fun_prop
    exact hseg.cthickening
  have hS_meas : MeasurableSet S.carrier :=
    hS_compact.measurableSet
  have hfin_E : volume E < ⊤ := by
    exact (measure_mono hE_T).trans_lt hT_compact.measure_lt_top
  have hfin_S : S.volume < ⊤ := by
    exact hS_compact.measure_lt_top
  have hfin_SE :
      volume (S.carrier ∩ Metric.cthickening rho E) < ⊤ := by
    exact
      (measure_mono Set.inter_subset_left).trans_lt
        hS_compact.measure_lt_top
  have hdelta_one : delta ≤ 1 :=
    hdelta_rho.trans hrho_one
  have hfin_T : Kakeya.deltaTubeVolume delta < ⊤ :=
    (tube_volume_scaling.2.1 delta hdelta hdelta_one).2.lt_top
  let A : Set (Point3 × Point3) :=
    (E ×ˢ S.carrier) ∩ {p | dist p.1 p.2 ≤ rho}
  have hA_meas : MeasurableSet A := by
    have h1 : MeasurableSet (E ×ˢ S.carrier) :=
      hE_meas.prod hS_meas
    have h2 :
        MeasurableSet {p : Point3 × Point3 | dist p.1 p.2 ≤ rho} := by
      have hcont :
          Continuous (fun p : Point3 × Point3 => dist p.1 p.2) := by
        fun_prop
      exact hcont.measurable measurableSet_Iic
    exact h1.inter h2
  let f : Point3 × Point3 → ENNReal :=
    Set.indicator A (fun _ => (1 : ENNReal))
  have hf : Measurable f := measurable_const.indicator hA_meas
  have hf' : AEMeasurable f (volume.prod volume) :=
    hf.aemeasurable
  have h_tonelli :
      (∫⁻ x : Point3, ∫⁻ y : Point3, f (x, y)) =
        ∫⁻ y : Point3, ∫⁻ x : Point3, f (x, y) := by
    have h1 :
        (∫⁻ z : Point3 × Point3, f z) =
          ∫⁻ x : Point3, ∫⁻ y : Point3, f (x, y) :=
      MeasureTheory.lintegral_prod f hf'
    have h2 :
        (∫⁻ z : Point3 × Point3, f z) =
          ∫⁻ y : Point3, ∫⁻ x : Point3, f (x, y) :=
      MeasureTheory.lintegral_prod_symm f hf'
    exact h1.symm.trans h2
  let C1 : ENNReal :=
    ENNReal.ofReal (Real.pi * rho^3 / 6)
  let C2 : ENNReal :=
    ENNReal.ofReal (2 * Real.pi * delta^2 * rho)
  let targetSet : Set Point3 :=
    S.carrier ∩ Metric.cthickening rho E
  have hLHS_pointwise :
      ∀ x : Point3,
        (∫⁻ y : Point3, f (x, y)) =
          Set.indicator E
            (fun x => volume (S.carrier ∩ Metric.closedBall x rho)) x := by
    intro x
    by_cases hxE : x ∈ E
    · have h_set :
          {y : Point3 | (x, y) ∈ A} =
            S.carrier ∩ Metric.closedBall x rho := by
        ext y
        simp only [A, Set.mem_inter_iff, Set.mem_prod,
          Set.mem_setOf_eq, Metric.mem_closedBall]
        constructor
        · rintro ⟨⟨_hx, hyS⟩, hdist⟩
          exact ⟨hyS, by rwa [dist_comm]⟩
        · rintro ⟨hyS, hdist⟩
          exact ⟨⟨hxE, hyS⟩, by rwa [dist_comm]⟩
      have h_f :
          (fun y : Point3 => f (x, y)) =
            Set.indicator {y : Point3 | (x, y) ∈ A}
              (fun _ => (1 : ENNReal)) := by
        funext y
        rfl
      rw [h_f, h_set]
      have hSint_meas :
          MeasurableSet
            (S.carrier ∩ Metric.closedBall x rho) :=
        hS_meas.inter isClosed_closedBall.measurableSet
      have h :
          (∫⁻ y : Point3,
              Set.indicator
                (S.carrier ∩ Metric.closedBall x rho)
                (fun _ => (1 : ENNReal)) y) =
            volume (S.carrier ∩ Metric.closedBall x rho) := by
        rw [MeasureTheory.lintegral_indicator_const₀
          hSint_meas.nullMeasurableSet (1 : ENNReal)]
        <;> simp
      rw [h]
      <;> simp [hxE, Set.indicator]
    · have h_f :
          (fun y : Point3 => f (x, y)) =
            fun _ : Point3 => (0 : ENNReal) := by
        funext y
        simp [f, Set.indicator, A, hxE] <;> tauto
      rw [h_f]
      <;> simp [hxE, Set.indicator]
  have hLHS :
      (∫⁻ x : Point3, ∫⁻ y : Point3, f (x, y)) =
        ∫⁻ x : Point3,
          Set.indicator E
            (fun x => volume (S.carrier ∩ Metric.closedBall x rho)) x := by
    congr with x
    exact hLHS_pointwise x
  have hLHS_lower :
      (∫⁻ x : Point3,
          Set.indicator E
            (fun x => volume (S.carrier ∩ Metric.closedBall x rho)) x) ≥
        C1 * volume E := by
    have h1 :
        ∀ x : Point3,
          Set.indicator E
              (fun x => volume (S.carrier ∩ Metric.closedBall x rho)) x ≥
            Set.indicator E (fun _ : Point3 => C1) x := by
      intro x
      by_cases hx : x ∈ E
      · have h_density :
            volume (S.carrier ∩ Metric.closedBall x rho) ≥ C1 :=
          tube_ball_density_rho hrho S (hE_S hx)
        simp [hx, h_density]
      · simp [hx]
    have h2 := lintegral_mono (μ := volume) h1
    have h3 :
        (∫⁻ x : Point3,
            Set.indicator E (fun _ : Point3 => C1) x) =
          C1 * volume E := by
      rw [MeasureTheory.lintegral_indicator hE_meas
        (fun _ => C1)]
      <;> simp <;> ring
    rw [h3] at h2
    exact h2
  have hRHS_pointwise :
      ∀ y : Point3,
        (∫⁻ x : Point3, f (x, y)) =
          Set.indicator S.carrier
            (fun y => volume (E ∩ Metric.closedBall y rho)) y := by
    intro y
    by_cases hyS : y ∈ S.carrier
    · have h_set :
          {x : Point3 | (x, y) ∈ A} =
            E ∩ Metric.closedBall y rho := by
        ext x
        simp only [A, Set.mem_inter_iff, Set.mem_prod,
          Set.mem_setOf_eq, Metric.mem_closedBall]
        constructor
        · rintro ⟨⟨hxE, _hyS⟩, hdist⟩
          exact ⟨hxE, hdist⟩
        · rintro ⟨hxE, hdist⟩
          exact ⟨⟨hxE, hyS⟩, hdist⟩
      have h_f :
          (fun x : Point3 => f (x, y)) =
            Set.indicator {x : Point3 | (x, y) ∈ A}
              (fun _ => (1 : ENNReal)) := by
        funext x
        rfl
      rw [h_f, h_set]
      have hEint_meas :
          MeasurableSet (E ∩ Metric.closedBall y rho) :=
        hE_meas.inter isClosed_closedBall.measurableSet
      have h :
          (∫⁻ x : Point3,
              Set.indicator (E ∩ Metric.closedBall y rho)
                (fun _ => (1 : ENNReal)) x) =
            volume (E ∩ Metric.closedBall y rho) := by
        rw [MeasureTheory.lintegral_indicator_const₀
          hEint_meas.nullMeasurableSet (1 : ENNReal)]
        <;> simp
      rw [h]
      <;> simp [hyS, Set.indicator]
    · have h_f :
          (fun x : Point3 => f (x, y)) =
            fun _ : Point3 => (0 : ENNReal) := by
        funext x
        simp [f, Set.indicator, A, hyS] <;> tauto
      rw [h_f]
      <;> simp [hyS, Set.indicator]
  have hRHS :
      (∫⁻ y : Point3, ∫⁻ x : Point3, f (x, y)) =
        ∫⁻ y : Point3,
          Set.indicator S.carrier
            (fun y => volume (E ∩ Metric.closedBall y rho)) y := by
    congr with y
    exact hRHS_pointwise y
  have h_outside :
      ∀ y : Point3,
        y ∉ Metric.cthickening rho E →
          E ∩ Metric.closedBall y rho = ∅ := by
    intro y hy
    by_contra h
    rcases Set.nonempty_iff_ne_empty.mpr h with
      ⟨x, hxE, hxy⟩
    have hdist : dist x y ≤ rho := by
      simpa [Metric.mem_closedBall] using hxy
    exact hy
      (Metric.mem_cthickening_of_dist_le
        y x rho _ hxE (by rwa [dist_comm]))
  have hthick_meas :
      MeasurableSet (Metric.cthickening rho E) :=
    isClosed_cthickening.measurableSet
  have htarget_meas : MeasurableSet targetSet :=
    hS_meas.inter hthick_meas
  have hRHS_upper :
      ∀ y : Point3,
        Set.indicator S.carrier
            (fun y => volume (E ∩ Metric.closedBall y rho)) y ≤
          Set.indicator targetSet (fun _ : Point3 => C2) y := by
    intro y
    by_cases hyS : y ∈ S.carrier
    · by_cases hythick : y ∈ Metric.cthickening rho E
      · have h_in_target : y ∈ targetSet := ⟨hyS, hythick⟩
        have h_vol_E :
            volume (E ∩ Metric.closedBall y rho) ≤
              volume (T.carrier ∩ Metric.closedBall y rho) :=
          measure_mono (Set.inter_subset_inter_left _ hE_T)
        have h_vol_T :
            volume (T.carrier ∩ Metric.closedBall y rho) ≤ C2 := by
          have h :=
            tube_ball_intersection_volume hdelta hrho T y
          have h_eq :
              ENNReal.ofReal
                  (Real.pi * delta^2 * 2 * rho) = C2 := by
            unfold C2
            congr 1
            ring
          rwa [h_eq] at h
        rw [Set.indicator_of_mem hyS,
          Set.indicator_of_mem h_in_target]
        exact h_vol_E.trans h_vol_T
      · have h_empty :
            E ∩ Metric.closedBall y rho = ∅ :=
          h_outside y hythick
        simp [Set.indicator, hyS, hythick, h_empty]
    · simp [Set.indicator, hyS]
  have hRHS_bound :
      (∫⁻ y : Point3,
          Set.indicator S.carrier
            (fun y => volume (E ∩ Metric.closedBall y rho)) y) ≤
        C2 * volume targetSet := by
    have h2 := lintegral_mono (μ := volume) hRHS_upper
    have h3 :
        (∫⁻ y : Point3,
            Set.indicator targetSet (fun _ : Point3 => C2) y) =
          C2 * volume targetSet := by
      rw [MeasureTheory.lintegral_indicator htarget_meas
        (fun _ => C2)]
      <;> simp <;> ring
    rwa [h3] at h2
  have h_double_count :
      C1 * volume E ≤ C2 * volume targetSet := by
    calc
      C1 * volume E ≤
          ∫⁻ x : Point3,
            Set.indicator E
              (fun x => volume
                (S.carrier ∩ Metric.closedBall x rho)) x :=
        hLHS_lower
      _ = (∫⁻ x : Point3, ∫⁻ y : Point3, f (x, y)) :=
        hLHS.symm
      _ = (∫⁻ y : Point3, ∫⁻ x : Point3, f (x, y)) :=
        h_tonelli
      _ = ∫⁻ y : Point3,
          Set.indicator S.carrier
            (fun y => volume (E ∩ Metric.closedBall y rho)) y :=
        hRHS
      _ ≤ C2 * volume targetSet := hRHS_bound
  set vE : ℝ := (volume E).toReal
  set vS : ℝ := S.volume.toReal
  set vT : ℝ := (Kakeya.deltaTubeVolume delta).toReal
  set vSE : ℝ := (volume targetSet).toReal
  have hfin_vE : volume E ≠ ⊤ := hfin_E.ne
  have hfin_vS : S.volume ≠ ⊤ := hfin_S.ne
  have hfin_vT : Kakeya.deltaTubeVolume delta ≠ ⊤ :=
    hfin_T.ne
  have hfin_vSE : volume targetSet ≠ ⊤ := hfin_SE.ne
  have h_real_double :
      (Real.pi * rho^3 / 6) * vE ≤
        (2 * Real.pi * delta^2 * rho) * vSE := by
    have hfin_prod1 :
        C1 * volume E ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin_vE
    have hfin_prod2 :
        C2 * volume targetSet ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin_vSE
    have h3 :
        (C1 * volume E).toReal ≤
          (C2 * volume targetSet).toReal := by
      have h_eq1 :
          C1 * volume E =
            ENNReal.ofReal ((C1 * volume E).toReal) :=
        (ENNReal.ofReal_toReal hfin_prod1).symm
      have h_eq2 :
          C2 * volume targetSet =
            ENNReal.ofReal ((C2 * volume targetSet).toReal) :=
        (ENNReal.ofReal_toReal hfin_prod2).symm
      rw [h_eq1, h_eq2] at h_double_count
      rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h_double_count
      exact h_double_count
    have h1 :
        (C1 * volume E).toReal =
          C1.toReal * (volume E).toReal := by
      simp [ENNReal.toReal_mul]
    have h1' : C1.toReal = Real.pi * rho^3 / 6 := by
      simp [C1] <;> positivity
    have h1'' : (volume E).toReal = vE := by
      simp [vE]
    have h2 :
        (C2 * volume targetSet).toReal =
          C2.toReal * (volume targetSet).toReal := by
      simp [ENNReal.toReal_mul]
    have h2' :
        C2.toReal = 2 * Real.pi * delta^2 * rho := by
      simp [C2] <;> positivity
    have h2'' : (volume targetSet).toReal = vSE := by
      simp [vSE]
    rw [h1, h2, h1', h2', h1'', h2''] at h3
    exact h3
  have h_real2 :
      (Real.pi * rho^2 / 6) * vE ≤
        (2 * Real.pi * delta^2) * vSE := by
    have h :
        (Real.pi * rho^3 / 6) * vE =
          rho * ((Real.pi * rho^2 / 6) * vE) := by ring
    have h' :
        (2 * Real.pi * delta^2 * rho) * vSE =
          rho * ((2 * Real.pi * delta^2) * vSE) := by ring
    rw [h, h'] at h_real_double
    exact le_of_mul_le_mul_left h_real_double hrho
  have h_real3 :
      (3 * Real.pi / 100 * rho^2) * vE ≤
        (Real.pi * delta^2) * vSE := by
    calc
      (3 * Real.pi / 100 * rho^2) * vE =
          (18 / 100 : ℝ) *
            ((Real.pi * rho^2 / 6) * vE) := by ring
      _ ≤ (18 / 100 : ℝ) *
          ((2 * Real.pi * delta^2) * vSE) :=
        mul_le_mul_of_nonneg_left h_real2 (by norm_num)
      _ = (9 * Real.pi / 25 * delta^2) * vSE := by ring
      _ ≤ (Real.pi * delta^2) * vSE := by
        have h : (9 * Real.pi / 25 : ℝ) ≤ Real.pi := by
          linarith [Real.pi_pos]
        have h2 : 0 ≤ delta^2 * vSE := by positivity
        have h3 :
            (9 * Real.pi / 25 : ℝ) * (delta^2 * vSE) ≤
              Real.pi * (delta^2 * vSE) :=
          mul_le_mul_of_nonneg_right h h2
        convert h3 using 1 <;> ring
  have h_toReal_mono :
      ∀ {a b : ENNReal}, b ≠ ⊤ → a ≤ b → a.toReal ≤ b.toReal := by
    intro a b hb h
    exact ENNReal.toReal_mono hb h
  have hS_upper_real : vS ≤ 3 * Real.pi * rho^2 := by
    have hEq : S.volume = Kakeya.deltaTubeVolume rho :=
      tube_volume_scaling.1 rho S
    have hUpper := tube_volume_upper_pi hrho S
    rw [hEq] at hUpper
    have h2 :
        Kakeya.deltaTubeVolume rho ≤
          ENNReal.ofReal (3 * Real.pi * rho^2) := by
      have h : 1 + 2 * rho ≤ 3 := by linarith
      have hnonneg : 0 ≤ Real.pi * rho^2 := by positivity
      have hreal :
          Real.pi * rho^2 * (1 + 2 * rho) ≤
            3 * Real.pi * rho^2 := by
        nlinarith
      exact hUpper.trans (ENNReal.ofReal_mono hreal)
    have h5 :=
      h_toReal_mono ENNReal.ofReal_ne_top h2
    change S.volume.toReal ≤ 3 * Real.pi * rho^2
    rw [hEq]
    have h6 :
        (ENNReal.ofReal (3 * Real.pi * rho^2)).toReal =
          3 * Real.pi * rho^2 := by
      simp <;> positivity
    rwa [h6] at h5
  have hT_lower_real : Real.pi * delta^2 ≤ vT := by
    have hLower := tube_volume_lower_pi hdelta T
    have hEq : T.volume = Kakeya.deltaTubeVolume delta :=
      tube_volume_scaling.1 delta T
    rw [hEq] at hLower
    have h2 := h_toReal_mono hfin_vT hLower
    change Real.pi * delta^2 ≤
      (Kakeya.deltaTubeVolume delta).toReal
    have h3 :
        (ENNReal.ofReal (Real.pi * delta^2)).toReal =
          Real.pi * delta^2 := by
      simp <;> positivity
    rwa [h3] at h2
  have h_final_real :
      (1 / 100 : ℝ) * vE * vS ≤ vT * vSE := by
    calc
      (1 / 100 : ℝ) * vE * vS ≤
          (1 / 100 : ℝ) * vE *
            (3 * Real.pi * rho^2) := by
        gcongr <;> positivity
      _ = (3 * Real.pi / 100 * rho^2) * vE := by ring
      _ ≤ (Real.pi * delta^2) * vSE := h_real3
      _ ≤ vT * vSE := by
        gcongr <;> positivity
  let a : ENNReal :=
    ENNReal.ofReal (1 / 100 : ℝ) * volume E * S.volume
  let b : ENNReal :=
    Kakeya.deltaTubeVolume delta * volume targetSet
  have ha_ne_top : a ≠ ⊤ := by
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin_vE) hfin_vS
  have hb_ne_top : b ≠ ⊤ :=
    ENNReal.mul_ne_top hfin_vT hfin_vSE
  have h4 : a.toReal = (1 / 100 : ℝ) * vE * vS := by
    simp [a, vE, vS, ENNReal.toReal_mul]
  have h5 : b.toReal = vT * vSE := by
    simp [b, vT, vSE, ENNReal.toReal_mul]
  have h6 : a.toReal ≤ b.toReal := by
    rw [h4, h5]
    exact h_final_real
  exact (ENNReal.toReal_le_toReal ha_ne_top hb_ne_top).mp h6

end Kakeya.Assouad

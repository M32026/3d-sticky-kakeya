import MyLeanRepo.Kakeya.Assouad.Statements
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-! WZ2 Section 7: absolute-constant tube-volume scaling. -/

noncomputable section

open MeasureTheory Metric

namespace Kakeya.Assouad

private lemma IsometryEquiv.cthickening_image {α β : Type*}
    [PseudoEMetricSpace α] [PseudoEMetricSpace β]
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

private lemma deltaTube_volume_eq {delta : ℝ}
    (T : Kakeya.DeltaTube delta) :
    T.volume = Kakeya.deltaTubeVolume delta := by
  let e0 : Point3 := EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
  have he0 : ‖e0‖ = 1 := by simp [e0]
  have hnorm : ‖T.direction‖ = ‖e0‖ := by
    rw [T.direction_unit, he0]
  let A : Point3 ≃ₗᵢ[ℝ] Point3 :=
    Submodule.reflection (ℝ ∙ (T.direction - e0))ᗮ
  have hA : A T.direction = e0 :=
    Submodule.reflection_sub hnorm
  let translate : Point3 ≃ᵢ Point3 :=
    { toFun := fun x => x - T.base
      invFun := fun y => y + T.base
      left_inv := by intro x; simp
      right_inv := by intro y; simp
      isometry_toFun := by
        intro x y
        simp [edist_dist, dist_eq_norm] }
  let rigid : Point3 ≃ᵢ Point3 := translate.trans A
  have hrigid : ∀ x, rigid x = A (x - T.base) := by
    intro x
    rfl
  have hsegment :
      rigid '' Kakeya.unitSegment T.base T.direction =
        Kakeya.unitSegment 0 e0 := by
    ext y
    simp only [Kakeya.unitSegment, Set.mem_image]
    constructor
    · rintro ⟨x, ⟨t, ht, rfl⟩, rfl⟩
      refine ⟨t, ht, ?_⟩
      simp [hrigid, hA, A.map_smul]
    · rintro ⟨t, ht, rfl⟩
      refine ⟨T.base + t • T.direction, ⟨t, ht, rfl⟩, ?_⟩
      simp [hrigid, hA, A.map_smul]
  have hcarrier :
      rigid '' T.carrier =
        Metric.cthickening delta (Kakeya.unitSegment 0 e0) := by
    rw [Kakeya.DeltaTube.carrier,
      IsometryEquiv.cthickening_image rigid, hsegment]
  have hA_preserving : MeasurePreserving A volume volume :=
    A.measurePreserving
  have htranslate_preserving :
      MeasurePreserving translate volume volume :=
    measurePreserving_sub_right volume T.base
  have hpreserving : MeasurePreserving rigid volume volume :=
    hA_preserving.comp htranslate_preserving
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
  have hpreimage :
      rigid '' T.carrier = rigid.symm ⁻¹' T.carrier := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hz
      exact ⟨rigid.symm z, hz, rigid.apply_symm_apply z⟩
  have hvolume :
      volume (rigid '' T.carrier) = volume T.carrier := by
    rw [hpreimage]
    exact MeasurePreserving.measure_preimage_equiv
      (f := rigidMeasurable.symm) hpreserving_symm T.carrier
  rw [Kakeya.DeltaTube.volume, ← hvolume, hcarrier]
  rfl

/-- The indexed mass of a tube family is its nominal cardinality-volume mass. -/
theorem tubeFamily_mass_eq_nominal {delta : ℝ}
    (F : Kakeya.Streamlined.TubeFamily delta) :
    F.toBodyFamily.mass = F.nominalMass := by
  have hvolume :
      ∀ i : Fin F.card,
        (F.toBodyFamily.body i).volume =
          Kakeya.deltaTubeVolume delta := by
    intro i
    exact deltaTube_volume_eq (F.tube i)
  calc
    F.toBodyFamily.mass
        = ∑ i : Fin F.card,
            (F.toBodyFamily.body i).volume := by rfl
    _ = ∑ _i : Fin F.card,
          Kakeya.deltaTubeVolume delta := by
        apply Finset.sum_congr rfl
        intro i _
        exact hvolume i
    _ = (F.card : ENNReal) *
          Kakeya.deltaTubeVolume delta := by
        simp [Finset.sum_const]
    _ = F.nominalMass := by rfl

theorem volume_rectBox
    (lo hi : Fin 3 → ℝ) (hlohi : ∀ i, lo i ≤ hi i) :
    volume ((WithLp.toLp 2) '' Set.Icc lo hi) =
      ENNReal.ofReal
        ((hi 0 - lo 0) * (hi 1 - lo 1) * (hi 2 - lo 2)) := by
  let toLp : (Fin 3 → ℝ) → Point3 := WithLp.toLp 2
  have hpreserving : MeasurePreserving toLp :=
    PiLp.volume_preserving_toLp (ι := Fin 3)
  have hinjective : Function.Injective toLp := by
    intro x y hxy
    simpa [toLp, WithLp.toLp_injective] using hxy
  have hcontinuous : Continuous toLp :=
    PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 3 => ℝ)
  have himage_measurable : MeasurableSet (toLp '' Set.Icc lo hi) := by
    have himage :
        toLp '' Set.Icc lo hi =
          (fun x : Point3 => x.ofLp) ⁻¹' Set.Icc lo hi := by
      ext y
      simp only [toLp, Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨x, hx, rfl⟩
        simpa [WithLp.ofLp_toLp] using hx
      · intro hy
        exact ⟨y.ofLp, hy, by simp [WithLp.ofLp_toLp]⟩
    rw [himage]
    exact (PiLp.continuous_ofLp
      (p := 2) (β := fun _ : Fin 3 => ℝ)).measurable measurableSet_Icc
  have hvolume :
      volume (toLp '' Set.Icc lo hi) = volume (Set.Icc lo hi) := by
    calc
      volume (toLp '' Set.Icc lo hi)
          = Measure.map toLp volume (toLp '' Set.Icc lo hi) := by
            rw [hpreserving.map_eq]
      _ = volume (toLp ⁻¹' (toLp '' Set.Icc lo hi)) :=
        Measure.map_apply hcontinuous.measurable himage_measurable
      _ = volume (Set.Icc lo hi) := by
        rw [Set.preimage_image_eq _ hinjective]
  rw [hvolume, Real.volume_Icc_pi]
  simp [Fin.prod_univ_succ, ← ENNReal.ofReal_mul,
    sub_nonneg.mpr (hlohi 0), sub_nonneg.mpr (hlohi 1)]
  ring_nf

private lemma canonical_segment_compact :
    IsCompact (Kakeya.unitSegment 0
      (EuclideanSpace.single (0 : Fin 3) (1 : ℝ))) := by
  apply IsCompact.image isCompact_Icc
  fun_prop

private lemma canonical_volume_pos_finite
    {delta : ℝ} (hdelta : 0 < delta) :
    0 < Kakeya.deltaTubeVolume delta ∧
      Kakeya.deltaTubeVolume delta ≠ ⊤ := by
  let e0 : Point3 := EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
  let midpoint : Point3 := (1 / 2 : ℝ) • e0
  have hmid :
      midpoint ∈ Kakeya.unitSegment 0 e0 := by
    exact ⟨1 / 2, by norm_num, by simp [midpoint]⟩
  have hball :
      Metric.closedBall midpoint (delta / 2) ⊆
        Metric.cthickening delta (Kakeya.unitSegment 0 e0) := by
    intro x hx
    exact Metric.mem_cthickening_of_dist_le
      x midpoint delta _ hmid (by
        have := hx
        simpa [Metric.mem_closedBall] using
          (show dist x midpoint ≤ delta from by
            have : dist x midpoint ≤ delta / 2 := hx
            linarith))
  have hball_pos :
      0 < volume (Metric.closedBall midpoint (delta / 2)) := by
    rw [EuclideanSpace.volume_closedBall_fin_three]
    positivity
  have hpositive :
      0 < Kakeya.deltaTubeVolume delta := by
    exact hball_pos.trans_le (measure_mono hball)
  have hcompact :
      IsCompact (Metric.cthickening delta
        (Kakeya.unitSegment 0 e0)) := by
    exact canonical_segment_compact.cthickening
  exact ⟨hpositive, hcompact.measure_lt_top.ne⟩

lemma canonical_tube_subset_box
    {rho : ℝ} (hrho : 0 < rho) :
    Metric.cthickening rho
        (Kakeya.unitSegment 0
          (EuclideanSpace.single (0 : Fin 3) (1 : ℝ))) ⊆
      (WithLp.toLp 2) '' Set.Icc
        (fun i : Fin 3 =>
          match i with
          | 0 => -rho
          | 1 => -rho
          | 2 => -rho)
        (fun i : Fin 3 =>
          match i with
          | 0 => 1 + rho
          | 1 => rho
          | 2 => rho) := by
  intro x hx
  rw [canonical_segment_compact.cthickening_eq_biUnion_closedBall
    hrho.le] at hx
  rcases Set.mem_iUnion₂.mp hx with ⟨y, hy, hxy⟩
  rcases hy with ⟨t, ht, rfl⟩
  refine ⟨x.ofLp, ?_, by simp [WithLp.ofLp_toLp]⟩
  constructor <;> intro i
  · fin_cases i
    · have hcoord :=
        PiLp.dist_apply_le x
          ((0 : Point3) + t •
            EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) (0 : Fin 3)
      have habs :
          |x 0 - t| ≤ rho := by
        simpa [Real.dist_eq, Metric.mem_closedBall] using
          hcoord.trans hxy
      dsimp
      have habs' := abs_le.mp habs
      linarith [ht.1, habs'.1]
    · have hcoord :=
        PiLp.dist_apply_le x
          ((0 : Point3) + t •
            EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) (1 : Fin 3)
      have habs : |x 1| ≤ rho := by
        simpa [Real.dist_eq, Metric.mem_closedBall] using
          hcoord.trans hxy
      exact (abs_le.mp habs).1
    · have hcoord :=
        PiLp.dist_apply_le x
          ((0 : Point3) + t •
            EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) (2 : Fin 3)
      have habs : |x 2| ≤ rho := by
        simpa [Real.dist_eq, Metric.mem_closedBall] using
          hcoord.trans hxy
      exact (abs_le.mp habs).1
  · fin_cases i
    · have hcoord :=
        PiLp.dist_apply_le x
          ((0 : Point3) + t •
            EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) (0 : Fin 3)
      have habs :
          |x 0 - t| ≤ rho := by
        simpa [Real.dist_eq, Metric.mem_closedBall] using
          hcoord.trans hxy
      dsimp
      have habs' := abs_le.mp habs
      linarith [ht.2, habs'.2]
    · have hcoord :=
        PiLp.dist_apply_le x
          ((0 : Point3) + t •
            EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) (1 : Fin 3)
      have habs : |x 1| ≤ rho := by
        simpa [Real.dist_eq, Metric.mem_closedBall] using
          hcoord.trans hxy
      exact (abs_le.mp habs).2
    · have hcoord :=
        PiLp.dist_apply_le x
          ((0 : Point3) + t •
            EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) (2 : Fin 3)
      have habs : |x 2| ≤ rho := by
        simpa [Real.dist_eq, Metric.mem_closedBall] using
          hcoord.trans hxy
      exact (abs_le.mp habs).2

/-- Tight upper bound: canonical tube volume ≤ `(1+2ρ)·(2ρ)·(2ρ)`. -/
lemma canonical_volume_upper_tight
    {rho : ℝ} (hrho : 0 < rho) (hrho_one : rho ≤ 1) :
    Kakeya.deltaTubeVolume rho ≤
      ENNReal.ofReal ((1 + 2 * rho) * (2 * rho) * (2 * rho)) := by
  let lo : Fin 3 → ℝ := fun i =>
    match i with
    | 0 => -rho
    | 1 => -rho
    | 2 => -rho
  let hi : Fin 3 → ℝ := fun i =>
    match i with
    | 0 => 1 + rho
    | 1 => rho
    | 2 => rho
  have hlohi : ∀ i, lo i ≤ hi i := by
    intro i
    fin_cases i <;> dsimp [lo, hi] <;> linarith
  have hbox :
      volume (Metric.cthickening rho
        (Kakeya.unitSegment 0
          (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)))) ≤
      volume ((WithLp.toLp 2) '' Set.Icc lo hi) :=
    measure_mono (canonical_tube_subset_box hrho)
  rw [volume_rectBox lo hi hlohi] at hbox
  have hprod : (hi 0 - lo 0) * (hi 1 - lo 1) * (hi 2 - lo 2) = (1 + 2 * rho) * (2 * rho) * (2 * rho) := by
    simp [lo, hi] <;> ring
  rw [hprod] at hbox
  exact hbox

private lemma canonical_volume_upper
    {rho : ℝ} (hrho : 0 < rho) (hrho_one : rho ≤ 1) :
    Kakeya.deltaTubeVolume rho ≤
      12 * Kakeya.realRpowENN rho 2 := by
  let lo : Fin 3 → ℝ := fun i =>
    match i with
    | 0 => -rho
    | 1 => -rho
    | 2 => -rho
  let hi : Fin 3 → ℝ := fun i =>
    match i with
    | 0 => 1 + rho
    | 1 => rho
    | 2 => rho
  have hlohi : ∀ i, lo i ≤ hi i := by
    intro i
    fin_cases i <;> dsimp [lo, hi] <;> linarith
  have hbox :
      volume (Metric.cthickening rho
        (Kakeya.unitSegment 0
          (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)))) ≤
      volume ((WithLp.toLp 2) '' Set.Icc lo hi) :=
    measure_mono (canonical_tube_subset_box hrho)
  rw [volume_rectBox lo hi hlohi] at hbox
  have hbox' :
      volume (Metric.cthickening rho
        (Kakeya.unitSegment 0
          (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)))) ≤
        ENNReal.ofReal
          ((1 + 2 * rho) * (2 * rho) * (2 * rho)) := by
    convert hbox using 1 <;> simp [lo, hi] <;> ring_nf
  have hreal :
      (1 + 2 * rho) * (2 * rho) * (2 * rho) ≤
        12 * rho ^ 2 := by
    nlinarith [sq_nonneg rho]
  have hofReal :
      ENNReal.ofReal
          ((1 + 2 * rho) * (2 * rho) * (2 * rho)) ≤
        ENNReal.ofReal (12 * rho ^ 2) :=
    ENNReal.ofReal_mono hreal
  calc
    Kakeya.deltaTubeVolume rho
        ≤ ENNReal.ofReal
          ((1 + 2 * rho) * (2 * rho) * (2 * rho)) := by
      simpa [Kakeya.deltaTubeVolume] using hbox'
    _ ≤ ENNReal.ofReal (12 * rho ^ 2) := hofReal
    _ = 12 * Kakeya.realRpowENN rho 2 := by
      simp [Kakeya.realRpowENN,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 12)]

theorem tube_volume_scaling : TubeVolumeScalingStatement := by
  refine ⟨?_, ?_, ?_⟩
  · intro delta T
    exact deltaTube_volume_eq T
  · intro delta hdelta _
    exact canonical_volume_pos_finite hdelta
  · intro rho hrho hrho_one T
    have hT : T.volume = Kakeya.deltaTubeVolume rho :=
      deltaTube_volume_eq T
    have hupper := canonical_volume_upper hrho hrho_one
    rw [hT]
    calc
      Kakeya.deltaTubeVolume rho
          ≤ 12 * Kakeya.realRpowENN rho 2 := hupper
      _ ≤ 24 * Kakeya.realRpowENN rho 2 *
          Kakeya.deltaTubeVolume 1 := by
        have hone_le : (1 : ENNReal) ≤
            Kakeya.deltaTubeVolume 1 := by
          have hball :
              Metric.closedBall
                  ((1 / 2 : ℝ) •
                    EuclideanSpace.single (0 : Fin 3) (1 : ℝ))
                  1 ⊆
                Metric.cthickening 1
                  (Kakeya.unitSegment 0
                    (EuclideanSpace.single (0 : Fin 3) (1 : ℝ))) := by
            intro x hx
            exact Metric.mem_cthickening_of_dist_le
              x ((1 / 2 : ℝ) •
                EuclideanSpace.single (0 : Fin 3) (1 : ℝ))
              1 _ ⟨1 / 2, by norm_num, by simp⟩ (by
                have : dist x ((1 / 2 : ℝ) •
                    EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) ≤
                    1 := hx
                exact this)
          have hvol :
              volume (Metric.closedBall
                ((1 / 2 : ℝ) •
                  EuclideanSpace.single (0 : Fin 3) (1 : ℝ))
                1) ≤
              volume (Metric.cthickening 1
                (Kakeya.unitSegment 0
                  (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)))) :=
            measure_mono hball
          have hball_lower : (1 : ENNReal) ≤
              volume (Metric.closedBall
                ((1 / 2 : ℝ) •
                  EuclideanSpace.single (0 : Fin 3) (1 : ℝ))
                1) := by
            rw [EuclideanSpace.volume_closedBall_fin_three]
            have hreal : (1 : ℝ) ≤ Real.pi * 4 / 3 := by
              linarith [Real.pi_gt_three]
            simpa using ENNReal.ofReal_mono hreal
          exact hball_lower.trans hvol
        calc
          12 * Kakeya.realRpowENN rho 2
              ≤ 24 * Kakeya.realRpowENN rho 2 := by
                gcongr
                norm_num
          _ = 24 * Kakeya.realRpowENN rho 2 * 1 := by simp
          _ ≤ 24 * Kakeya.realRpowENN rho 2 *
              Kakeya.deltaTubeVolume 1 := by gcongr

end Kakeya.Assouad

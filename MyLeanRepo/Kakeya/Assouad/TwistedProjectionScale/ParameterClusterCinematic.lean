import MyLeanRepo.Kakeya.Assouad.CinematicFamilyFromSlope.UpperBound
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.CinematicBridge3D
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ExtendedCinematicFamily
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterClusterKatzTao
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterProjectionFiberStatement

/-!
# Weighted parameter clusters to cinematic curves

The collapsed parameter normalization is `(a/24,b/24,d/4)`.  This module
records the exact fixed distortion needed to compare the geometric cluster
scale with the cinematic `C²` scale.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Kakeya.Assouad

/-- The cinematic curve represented by one normalized collapsed center. -/
def halfParameterSlopeCurve
    (f : SlopeFunction) (p : Point 3) :
    Kakeya.Cinematic.C2Function :=
  slopeCurve f (24 * p 0) (24 * p 1) (4 * p 2)

/-- The finite cinematic family represented by normalized collapsed centers. -/
def halfParameterCinematicFamily
    (f : SlopeFunction) (points : DiscreteSet 3) :
    Kakeya.Cinematic.FiniteFunctionFamily :=
  let image :=
    points.image (halfParameterSlopeCurve f)
  ⟨(image : Set Kakeya.Cinematic.C2Function), Finset.finite_toSet image⟩

/-- One tube's raw slope curve agrees with its collapsed parameter point. -/
lemma halfParameterSlopeCurve_tubeParameterPoint3
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (f : SlopeFunction) (i : Fin F.card) :
    halfParameterSlopeCurve f (tubeParameterPoint3 i) =
      slopeCurve f
        (tubeParams i).a (tubeParams i).b (tubeParams i).d := by
  simp [halfParameterSlopeCurve, tubeParameterPoint3, point3] <;> ring_nf

/--
Normalized parameter distance controls cinematic `C²` distance with the
fixed factor `260`.
-/
lemma halfParameterSlopeCurve_c2Distance_le
    (f : SlopeFunction) (h_ns : f.IsNonsingular) (h0 : f 0 = 0)
    (p q : Point 3) :
    Kakeya.Cinematic.c2Distance
        (halfParameterSlopeCurve f p)
        (halfParameterSlopeCurve f q) ≤
      260 * dist p q := by
  have hcoord0 : |p 0 - q 0| ≤ dist p q :=
    PiLp.dist_apply_le p q (0 : Fin 3)
  have hcoord1 : |p 1 - q 1| ≤ dist p q :=
    PiLp.dist_apply_le p q (1 : Fin 3)
  have hcoord2 : |p 2 - q 2| ≤ dist p q :=
    PiLp.dist_apply_le p q (2 : Fin 3)
  have hp0 : |24 * p 0 - 24 * q 0| ≤ 24 * dist p q := by
    calc
      |24 * p 0 - 24 * q 0| = 24 * |p 0 - q 0| := by
        rw [← mul_sub, abs_mul]
        norm_num
      _ ≤ 24 * dist p q := by gcongr
  have hp1 : |24 * p 1 - 24 * q 1| ≤ 24 * dist p q := by
    calc
      |24 * p 1 - 24 * q 1| = 24 * |p 1 - q 1| := by
        rw [← mul_sub, abs_mul]
        norm_num
      _ ≤ 24 * dist p q := by gcongr
  have hp2 : |4 * p 2 - 4 * q 2| ≤ 4 * dist p q := by
    calc
      |4 * p 2 - 4 * q 2| = 4 * |p 2 - q 2| := by
        rw [← mul_sub, abs_mul]
        norm_num
      _ ≤ 4 * dist p q := by gcongr
  have hupper :=
    slopeCurve_c2Distance_le f h_ns h0
      (24 * p 0) (24 * p 1) (4 * p 2)
      (24 * q 0) (24 * q 1) (4 * q 2)
  dsimp only [halfParameterSlopeCurve]
  calc
    Kakeya.Cinematic.c2Distance
        (slopeCurve f (24 * p 0) (24 * p 1) (4 * p 2))
        (slopeCurve f (24 * q 0) (24 * q 1) (4 * q 2))
        ≤ 5 *
          (|24 * p 0 - 24 * q 0| +
            |24 * p 1 - 24 * q 1| +
            |4 * p 2 - 4 * q 2|) := hupper
    _ ≤ 5 * (24 * dist p q + 24 * dist p q + 4 * dist p q) := by
      gcongr
    _ = 260 * dist p q := by ring

/--
The half-parameter cinematic map has a uniform inverse Lipschitz bound.
-/
lemma halfParameterSlopeCurve_dist_le
    (f : SlopeFunction) (h_ns : f.IsNonsingular) (h0 : f 0 = 0)
    (p q : Point 3) :
    dist p q ≤
      125 * Kakeya.Cinematic.c2Distance
        (halfParameterSlopeCurve f p)
        (halfParameterSlopeCurve f q) := by
  have hlower :=
    slopeCurve_c2Distance_ge3 f h_ns h0
      (24 * p 0) (24 * p 1) (4 * p 2)
      (24 * q 0) (24 * q 1) (4 * q 2)
  have habs0 :
      |24 * p 0 - 24 * q 0| = 24 * |p 0 - q 0| := by
    rw [← mul_sub, abs_mul]
    norm_num
  have habs1 :
      |24 * p 1 - 24 * q 1| = 24 * |p 1 - q 1| := by
    rw [← mul_sub, abs_mul]
    norm_num
  have habs2 :
      |4 * p 2 - 4 * q 2| = 4 * |p 2 - q 2| := by
    rw [← mul_sub, abs_mul]
    norm_num
  rw [habs0, habs1, habs2] at hlower
  have hl1 :=
    dist3_le_L1 p q
  have hraw :
      4 * dist p q ≤
        24 * |p 0 - q 0| +
          24 * |p 1 - q 1| +
          4 * |p 2 - q 2| := by
    calc
      4 * dist p q ≤
          4 * (|p 0 - q 0| + |p 1 - q 1| + |p 2 - q 2|) := by
        gcongr
      _ ≤
          24 * |p 0 - q 0| +
            24 * |p 1 - q 1| +
            4 * |p 2 - q 2| := by
        nlinarith [abs_nonneg (p 0 - q 0), abs_nonneg (p 1 - q 1)]
  have hscaled :
      (44 / 2500 : ℝ) * dist p q ≤
        Kakeya.Cinematic.c2Distance
          (halfParameterSlopeCurve f p)
          (halfParameterSlopeCurve f q) := by
    dsimp only [halfParameterSlopeCurve]
    calc
      (44 / 2500 : ℝ) * dist p q =
          (11 / 2500 : ℝ) * (4 * dist p q) := by ring
      _ ≤
          (11 / 2500 : ℝ) *
            (24 * |p 0 - q 0| +
              24 * |p 1 - q 1| +
              4 * |p 2 - q 2|) := by
        gcongr
      _ ≤
          Kakeya.Cinematic.c2Distance
            (slopeCurve f (24 * p 0) (24 * p 1) (4 * p 2))
            (slopeCurve f (24 * q 0) (24 * q 1) (4 * q 2)) :=
        hlower
  calc
    dist p q = 1 * dist p q := by ring
    _ ≤ (125 * (44 / 2500 : ℝ)) * dist p q := by
      gcongr
      norm_num
    _ = 125 * ((44 / 2500 : ℝ) * dist p q) := by ring
    _ ≤
        125 * Kakeya.Cinematic.c2Distance
          (halfParameterSlopeCurve f p)
          (halfParameterSlopeCurve f q) := by
      gcongr

/--
Katz--Tao non-concentration transfers from normalized half-parameters to the
finite cinematic family with one fixed absolute constant.
-/
lemma halfParameterCinematicFamily_katzTao
    (f : SlopeFunction) (h_ns : f.IsNonsingular) (h0 : f 0 = 0)
    (points : DiscreteSet 3)
    (cinematicScale : ℝ)
    (hscale : 0 < cinematicScale)
    (hscale_one : cinematicScale ≤ 1)
    (hKT : points.IsKatzTao cinematicScale 1 100)
    (hunit : points.IsInUnitBall) :
    HasCinematicKatzTaoBound
      (halfParameterCinematicFamily f points)
      cinematicScale 25000 := by
  let phi : Point 3 → Kakeya.Cinematic.C2Function :=
    halfParameterSlopeCurve f
  let family :=
    halfParameterCinematicFamily f points
  have hfamily :
      family.carrier = phi '' points := by
    simp [family, halfParameterCinematicFamily, phi]
  have hpoints_card :
      (points.card : ℝ) ≤ 100 / cinematicScale :=
    unitBall_global_card points cinematicScale
      hscale hscale_one hKT hunit
  have hfamily_card :
      family.card ≤ points.card := by
    have himage :
        phi '' (points : Set (Point 3)) =
          (points.image phi : Set Kakeya.Cinematic.C2Function) := by
      ext g
      simp [Set.mem_image, Finset.mem_image]
    have hncard :
        family.carrier.ncard =
          (points.image phi).card := by
      rw [hfamily, himage]
      exact Set.ncard_coe_finset _
    have hcard :
        (points.image phi).card ≤ points.card :=
      Finset.card_image_le
    simpa [Kakeya.Cinematic.FiniteFunctionFamily.card, hncard] using hcard
  constructor
  · have hreal :
        (family.card : ℝ) ≤ (points.card : ℝ) := by
      exact_mod_cast hfamily_card
    calc
      (family.card : ℝ) ≤ (points.card : ℝ) := hreal
      _ ≤ 100 / cinematicScale := hpoints_card
      _ ≤ 25000 / cinematicScale := by
        gcongr
        norm_num
  · intro center r hr_scale hr_one
    let preimage : Finset (Point 3) :=
      points.filter fun p =>
        phi p ∈ Kakeya.Cinematic.c2Ball center r
    have hpreimage_subset :
        preimage ⊆ points :=
      Finset.filter_subset _ _
    have himage :
        family.carrier ∩ Kakeya.Cinematic.c2Ball center r =
          phi '' preimage := by
      rw [hfamily]
      ext g
      simp only [preimage, Set.mem_inter_iff, Set.mem_image,
        Finset.mem_coe, Finset.mem_filter]
      constructor
      · rintro ⟨⟨p, hp, rfl⟩, hball⟩
        exact ⟨p, ⟨hp, hball⟩, rfl⟩
      · rintro ⟨p, ⟨hp, hball⟩, rfl⟩
        exact ⟨⟨p, hp, rfl⟩, hball⟩
    have hncard :
        (family.carrier ∩
            Kakeya.Cinematic.c2Ball center r).ncard ≤
          preimage.card := by
      rw [himage]
      calc
        (phi '' (preimage : Set (Point 3))).ncard ≤
            (preimage : Set (Point 3)).ncard :=
          Set.ncard_image_le
            (s := (preimage : Set (Point 3))) (f := phi)
        _ = preimage.card := Set.ncard_coe_finset _
    by_cases hempty : preimage = ∅
    · have hzero :
          (family.carrier ∩
              Kakeya.Cinematic.c2Ball center r).ncard = 0 := by
        rw [hempty] at hncard
        simp at hncard
        omega
      rw [hzero]
      norm_num only [Nat.cast_zero]
      exact mul_nonneg (by norm_num) (div_nonneg (by linarith) hscale.le)
    · rcases Finset.nonempty_iff_ne_empty.mpr hempty with
        ⟨p0, hp0⟩
      have hr : 0 < r :=
        hscale.trans_le hr_scale
      let radius : ℝ := 250 * r
      have hball :
          ∀ p ∈ preimage, dist p p0 ≤ radius := by
        intro p hp
        have hp_ball :
            phi p ∈ Kakeya.Cinematic.c2Ball center r :=
          (Finset.mem_filter.mp hp).2
        have hp0_ball :
            phi p0 ∈ Kakeya.Cinematic.c2Ball center r :=
          (Finset.mem_filter.mp hp0).2
        have hcurve :
            Kakeya.Cinematic.c2Distance (phi p) (phi p0) ≤
              2 * r := by
          have htriangle :=
            dist_triangle (phi p) center (phi p0)
          have hp_le :
              dist (phi p) center ≤ r := by
            simpa [Kakeya.Cinematic.c2Distance_eq_dist] using hp_ball
          have hp0_le :
              dist center (phi p0) ≤ r := by
            simpa [Kakeya.Cinematic.c2Distance_eq_dist, dist_comm] using
              hp0_ball
          simpa [Kakeya.Cinematic.c2Distance_eq_dist] using
            htriangle.trans (by linarith)
        have hinverse :=
          halfParameterSlopeCurve_dist_le f h_ns h0 p p0
        dsimp only [phi] at hinverse hcurve
        dsimp only [radius]
        linarith
      have hpreimage_ball :
          preimage ⊆
            points.filter fun p => dist p p0 ≤ radius := by
        intro p hp
        exact
          Finset.mem_filter.mpr
            ⟨hpreimage_subset hp, hball p hp⟩
      have hcard :
          preimage.card ≤
            (points.filter fun p => dist p p0 ≤ radius).card :=
        Finset.card_le_card hpreimage_ball
      by_cases hradius_one : radius ≤ 1
      · have hradius_scale :
            cinematicScale ≤ radius := by
          dsimp only [radius]
          nlinarith
        have hKT_ball :=
          hKT p0 radius hradius_scale hradius_one
        have hKT_card :
            ((points.filter fun p => dist p p0 ≤ radius).card :
                ENNReal) ≤
              100 * Kakeya.realRpowENN
                (radius / cinematicScale) 1 := by
          simpa [DiscreteSet.ballCount] using hKT_ball
        have hpreimage_real :
            (preimage.card : ℝ) ≤
              25000 * (r / cinematicScale) := by
          have hcard_enn :
              (preimage.card : ENNReal) ≤
                100 * Kakeya.realRpowENN
                  (radius / cinematicScale) 1 := by
            have hcard_cast :
                (preimage.card : ENNReal) ≤
                  ((points.filter fun p =>
                    dist p p0 ≤ radius).card : ENNReal) := by
              exact_mod_cast hcard
            exact hcard_cast.trans hKT_card
          have hrpow :
              Kakeya.realRpowENN
                  (radius / cinematicScale) 1 =
                ENNReal.ofReal (radius / cinematicScale) := by
            simp [Kakeya.realRpowENN, Real.rpow_one]
          rw [hrpow] at hcard_enn
          have hmul :
              (100 : ENNReal) *
                  ENNReal.ofReal (radius / cinematicScale) =
                ENNReal.ofReal
                  (100 * (radius / cinematicScale)) := by
            rw [show (100 : ENNReal) =
                ENNReal.ofReal (100 : ℝ) by norm_num]
            exact
              (ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 100)).symm
          rw [hmul] at hcard_enn
          have hcard_ofReal :
              (preimage.card : ENNReal) =
                ENNReal.ofReal (preimage.card : ℝ) := by
            simp
          rw [hcard_ofReal] at hcard_enn
          have hreal :
              (preimage.card : ℝ) ≤
                100 * (radius / cinematicScale) :=
            (ENNReal.ofReal_le_ofReal_iff
              (mul_nonneg (by norm_num)
                (div_nonneg (by
                  dsimp only [radius]
                  positivity) hscale.le))).mp hcard_enn
          calc
            (preimage.card : ℝ) ≤
                100 * (radius / cinematicScale) := hreal
            _ = 25000 * (r / cinematicScale) := by
              dsimp only [radius]
              field_simp [hscale.ne']
              ring
        have hncard_real :
            ((family.carrier ∩
                Kakeya.Cinematic.c2Ball center r).ncard : ℝ) ≤
              (preimage.card : ℝ) := by
          exact_mod_cast hncard
        exact hncard_real.trans hpreimage_real
      · have hradius_large : 1 < radius := by
          linarith
        have hpreimage_real :
            (preimage.card : ℝ) ≤
              (points.card : ℝ) := by
          exact_mod_cast
            Finset.card_le_card hpreimage_subset
        have hglobal :
            (points.card : ℝ) ≤
              25000 * (r / cinematicScale) := by
          calc
            (points.card : ℝ) ≤
                100 / cinematicScale := hpoints_card
            _ ≤ 25000 * (r / cinematicScale) := by
              have hr_large : 1 / 250 < r := by
                dsimp only [radius] at hradius_large
                linarith
              field_simp [hscale.ne']
              nlinarith
        have hncard_real :
            ((family.carrier ∩
                Kakeya.Cinematic.c2Ball center r).ncard : ℝ) ≤
              (preimage.card : ℝ) := by
          exact_mod_cast hncard
        exact hncard_real.trans (hpreimage_real.trans hglobal)

/--
A normalized half-box center represents a curve in the fixed extended
cinematic family.
-/
lemma halfParameterSlopeCurve_mem_extended
    (f : SlopeFunction) (p : Point 3)
    (hp :
      |p 0| ≤ 1 / 2 ∧
        |p 1| ≤ 1 / 2 ∧
        |p 2| ≤ 1 / 2) :
    halfParameterSlopeCurve f p ∈ extendedSlopeCurveFamily f := by
  let q : Fin 3 → ℝ := fun i =>
    if i = 0 then 24 * p 0
    else if i = 1 then 24 * p 1
    else 4 * p 2
  have hq0 : q 0 = 24 * p 0 := by simp [q]
  have hq1 : q 1 = 24 * p 1 := by simp [q]
  have hq2 : q 2 = 4 * p 2 := by simp [q]
  have hq : q ∈ extendedParamBox := by
    simp only [extendedParamBox, Set.mem_setOf_eq]
    constructor
    · rw [hq0, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 24)]
      linarith [hp.1]
    · constructor
      · rw [hq1, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 24)]
        linarith [hp.2.1]
      · rw [hq2, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
        linarith [hp.2.2]
  refine ⟨q, hq, ?_⟩
  simp [halfParameterSlopeCurve, hq0, hq1, hq2]

/--
Every selected weighted-cluster center represents a curve in the fixed
extended cinematic family.
-/
lemma parameterClusterKatzTao_family_subset_extended
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C lambda : ENNReal}
    {clusterScale cinematicScale s : ℝ}
    {clustered :
      TubeParameterClusterFrostmanData
        F Y C lambda clusterScale}
    (data :
      TubeParameterClusterKatzTaoData
        (cinematicScale := cinematicScale) (s := s) clustered)
    (hparams :
      ∀ i : Fin F.card,
        |(tubeParams i).a| ≤ 12 ∧
          |(tubeParams i).b| ≤ 12 ∧
          |(tubeParams i).c| ≤ 2 ∧
          |(tubeParams i).d| ≤ 2)
    (f : SlopeFunction) :
    (halfParameterCinematicFamily f data.points).carrier ⊆
      extendedSlopeCurveFamily f := by
  intro g hg
  rcases Finset.mem_image.mp hg with ⟨p, hp, rfl⟩
  rcases data.center_source p hp with ⟨i, rfl⟩
  apply halfParameterSlopeCurve_mem_extended
  have hi := hparams i
  have h_eval0 :
      (tubeParameterPoint3 i) 0 = (tubeParams i).a / 24 := by
    simp [tubeParameterPoint3, point3]
  have h_eval1 :
      (tubeParameterPoint3 i) 1 = (tubeParams i).b / 24 := by
    simp [tubeParameterPoint3, point3]
  have h_eval2 :
      (tubeParameterPoint3 i) 2 = (tubeParams i).d / 4 := by
    simp [tubeParameterPoint3, point3]
  rw [h_eval0, h_eval1, h_eval2]
  constructor
  · rw [abs_div]
    norm_num
    linarith [hi.1]
  · constructor
    · rw [abs_div]
      norm_num
      linarith [hi.2.1]
    · rw [abs_div]
      norm_num
      linarith [hi.2.2.2]

/--
The raw curve of every retained tube lies within the cinematic scale of its
assigned weighted-cluster center.
-/
lemma parameterClusterKatzTao_assignment_close
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C lambda : ENNReal}
    {clusterScale cinematicScale s : ℝ}
    {clustered :
      TubeParameterClusterFrostmanData
        F Y C lambda clusterScale}
    (data :
      TubeParameterClusterKatzTaoData
        (cinematicScale := cinematicScale) (s := s) clustered)
    (f : SlopeFunction) (h_ns : f.IsNonsingular) (h0 : f 0 = 0)
    (hdistortion : 260 * clusterScale ≤ cinematicScale) :
    ∀ i, data.shading.carrier i ≠ ∅ →
      Kakeya.Cinematic.c2Distance
          (slopeCurve f
            (tubeParams i).a (tubeParams i).b (tubeParams i).d)
          (halfParameterSlopeCurve f (clustered.assign i)) ≤
        cinematicScale := by
  intro i hi
  rw [← halfParameterSlopeCurve_tubeParameterPoint3 f i]
  calc
    Kakeya.Cinematic.c2Distance
        (halfParameterSlopeCurve f (tubeParameterPoint3 i))
        (halfParameterSlopeCurve f (clustered.assign i)) ≤
        260 * dist (tubeParameterPoint3 i) (clustered.assign i) :=
      halfParameterSlopeCurve_c2Distance_le f h_ns h0 _ _
    _ ≤ 260 * clusterScale := by
      gcongr
      exact data.assign_close i hi
    _ ≤ cinematicScale := hdistortion

/--
The selected weighted-cluster centers satisfy the cinematic Katz--Tao bound
required by the PYZ input.
-/
lemma parameterClusterKatzTao_cinematic_katzTao
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C lambda : ENNReal}
    {clusterScale cinematicScale s : ℝ}
    {clustered :
      TubeParameterClusterFrostmanData
        F Y C lambda clusterScale}
    (data :
      TubeParameterClusterKatzTaoData
        (cinematicScale := cinematicScale) (s := s) clustered)
    (f : SlopeFunction) (h_ns : f.IsNonsingular) (h0 : f 0 = 0)
    (hcinematic : 0 < cinematicScale)
    (hcinematic_one : cinematicScale ≤ 1) :
    HasCinematicKatzTaoBound
      (halfParameterCinematicFamily f data.points)
      cinematicScale 25000 := by
  apply halfParameterCinematicFamily_katzTao
    f h_ns h0 data.points cinematicScale
    hcinematic hcinematic_one data.points_katzTao
  intro p hp
  exact clustered.points_in_unitBall p (data.points_subset hp)

/--
The fixed cinematic Katz--Tao bound passes to finite subfamilies.
-/
lemma cinematicKatzTao_mono
    {small large : Kakeya.Cinematic.FiniteFunctionFamily}
    {scale constant : ℝ}
    (hsub : small.carrier ⊆ large.carrier)
    (hlarge : HasCinematicKatzTaoBound large scale constant) :
    HasCinematicKatzTaoBound small scale constant := by
  constructor
  · have hcard :
        small.carrier.ncard ≤ large.carrier.ncard :=
      Set.ncard_le_ncard hsub large.finite
    have hcard_real :
        (small.card : ℝ) ≤ (large.card : ℝ) := by
      exact_mod_cast hcard
    exact hcard_real.trans hlarge.1
  · intro center r hr_scale hr_one
    have hball :
        small.carrier ∩ Kakeya.Cinematic.c2Ball center r ⊆
          large.carrier ∩ Kakeya.Cinematic.c2Ball center r := by
      intro g hg
      exact ⟨hsub hg.1, hg.2⟩
    have hncard :
        (small.carrier ∩
            Kakeya.Cinematic.c2Ball center r).ncard ≤
          (large.carrier ∩
            Kakeya.Cinematic.c2Ball center r).ncard :=
      Set.ncard_le_ncard hball
        (large.finite.subset Set.inter_subset_left)
    have hncard_real :
        ((small.carrier ∩
            Kakeya.Cinematic.c2Ball center r).ncard : ℝ) ≤
          ((large.carrier ∩
            Kakeya.Cinematic.c2Ball center r).ncard : ℝ) := by
      exact_mod_cast hncard
    exact hncard_real.trans
      (hlarge.2 center r hr_scale hr_one)

/--
The separated cinematic family and honest tube-cover radius produced by one
weighted cluster package.
-/
structure TubeParameterClusterCinematicData
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C lambda : ENNReal}
    {clusterScale cinematicScale s : ℝ}
    {clustered :
      TubeParameterClusterFrostmanData
        F Y C lambda clusterScale}
    (data :
      TubeParameterClusterKatzTaoData
        (cinematicScale := cinematicScale) (s := s) clustered)
    (f : SlopeFunction) where
  family : Kakeya.Cinematic.FiniteFunctionFamily
  family_subset_extended :
    family.carrier ⊆ extendedSlopeCurveFamily f
  family_separated :
    IsCinematicDeltaSeparated family cinematicScale
  family_katzTao :
    HasCinematicKatzTaoBound family cinematicScale 25000
  tube_cover :
    ∀ i, data.shading.carrier i ≠ ∅ →
      ∃ g ∈ family.carrier,
        Kakeya.Cinematic.c2Distance
            (slopeCurve f
              (tubeParams i).a (tubeParams i).b (tubeParams i).d)
            g ≤
          2 * cinematicScale

/--
Greedily separate the cinematic image of the selected weighted-cluster
centers.  The second covering step costs exactly one additional
`cinematicScale`.
-/
theorem parameterClusterKatzTao_cinematic_selection
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C lambda : ENNReal}
    {clusterScale cinematicScale s : ℝ}
    {clustered :
      TubeParameterClusterFrostmanData
        F Y C lambda clusterScale}
    (data :
      TubeParameterClusterKatzTaoData
        (cinematicScale := cinematicScale) (s := s) clustered)
    (hparams :
      ∀ i : Fin F.card,
        |(tubeParams i).a| ≤ 12 ∧
          |(tubeParams i).b| ≤ 12 ∧
          |(tubeParams i).c| ≤ 2 ∧
          |(tubeParams i).d| ≤ 2)
    (f : SlopeFunction) (h_ns : f.IsNonsingular) (h0 : f 0 = 0)
    (hcinematic : 0 < cinematicScale)
    (hcinematic_one : cinematicScale ≤ 1)
    (hdistortion : 260 * clusterScale ≤ cinematicScale) :
    Nonempty (TubeParameterClusterCinematicData data f) := by
  let full :=
    halfParameterCinematicFamily f data.points
  have hfull_extended :
      full.carrier ⊆ extendedSlopeCurveFamily f :=
    parameterClusterKatzTao_family_subset_extended data hparams f
  have hfull_katzTao :
      HasCinematicKatzTaoBound full cinematicScale 25000 :=
    parameterClusterKatzTao_cinematic_katzTao
      data f h_ns h0 hcinematic hcinematic_one
  rcases exists_greedy_separated3
      hcinematic full.toFinset with
    ⟨selected, hselected_sub, hselected_sep, hselected_cover⟩
  let family : Kakeya.Cinematic.FiniteFunctionFamily :=
    ⟨(selected : Set Kakeya.Cinematic.C2Function),
      Finset.finite_toSet selected⟩
  have hfamily_sub :
      family.carrier ⊆ full.carrier := by
    have hfull :
        full.carrier =
          (full.toFinset : Set Kakeya.Cinematic.C2Function) :=
      (Set.Finite.coe_toFinset full.finite).symm
    rw [hfull]
    exact_mod_cast hselected_sub
  have hfamily_extended :
      family.carrier ⊆ extendedSlopeCurveFamily f :=
    hfamily_sub.trans hfull_extended
  have hfamily_separated :
      IsCinematicDeltaSeparated family cinematicScale := by
    intro g hg h hh hne
    exact hselected_sep g hg h hh hne
  have hfamily_katzTao :
      HasCinematicKatzTaoBound family cinematicScale 25000 :=
    cinematicKatzTao_mono hfamily_sub hfull_katzTao
  have htube_cover :
      ∀ i, data.shading.carrier i ≠ ∅ →
        ∃ g ∈ family.carrier,
          Kakeya.Cinematic.c2Distance
              (slopeCurve f
                (tubeParams i).a (tubeParams i).b (tubeParams i).d)
              g ≤
            2 * cinematicScale := by
    intro i hi
    have hcenter_mem :
        halfParameterSlopeCurve f (clustered.assign i) ∈
          full.toFinset := by
      have hpoints :
          clustered.assign i ∈ data.points :=
        data.assign_mem i hi
      have hcarrier :
          halfParameterSlopeCurve f (clustered.assign i) ∈
            full.carrier := by
        exact Finset.mem_image.mpr
          ⟨clustered.assign i, hpoints, rfl⟩
      have hfull :
          full.carrier =
            (full.toFinset : Set Kakeya.Cinematic.C2Function) :=
        (Set.Finite.coe_toFinset full.finite).symm
      rw [hfull] at hcarrier
      exact_mod_cast hcarrier
    rcases hselected_cover
        (halfParameterSlopeCurve f (clustered.assign i))
        hcenter_mem with
      ⟨g, hg, hgclose⟩
    have hg_family : g ∈ family.carrier := by
      exact_mod_cast hg
    have htube_close :
        Kakeya.Cinematic.c2Distance
            (slopeCurve f
              (tubeParams i).a (tubeParams i).b (tubeParams i).d)
            (halfParameterSlopeCurve f (clustered.assign i)) ≤
          cinematicScale :=
      parameterClusterKatzTao_assignment_close
        data f h_ns h0 hdistortion i hi
    have htriangle :=
      dist_triangle
        (slopeCurve f
          (tubeParams i).a (tubeParams i).b (tubeParams i).d)
        (halfParameterSlopeCurve f (clustered.assign i)) g
    have hgclose_le :
        Kakeya.Cinematic.c2Distance
            (halfParameterSlopeCurve f (clustered.assign i)) g ≤
          cinematicScale := by
      simpa [Kakeya.Cinematic.c2Distance_eq_dist] using hgclose.le
    have htube_dist :
        dist
            (slopeCurve f
              (tubeParams i).a (tubeParams i).b (tubeParams i).d)
            (halfParameterSlopeCurve f (clustered.assign i)) ≤
          cinematicScale := by
      simpa [Kakeya.Cinematic.c2Distance_eq_dist] using htube_close
    have hg_dist :
        dist (halfParameterSlopeCurve f (clustered.assign i)) g ≤
          cinematicScale := by
      simpa [Kakeya.Cinematic.c2Distance_eq_dist] using hgclose_le
    refine ⟨g, hg_family, ?_⟩
    have hsum :
        dist
              (slopeCurve f
                (tubeParams i).a (tubeParams i).b (tubeParams i).d)
              (halfParameterSlopeCurve f (clustered.assign i)) +
            dist (halfParameterSlopeCurve f (clustered.assign i)) g ≤
          2 * cinematicScale := by
      calc
        _ ≤ cinematicScale + cinematicScale :=
          add_le_add htube_dist hg_dist
        _ = 2 * cinematicScale := by ring
    simpa [Kakeya.Cinematic.c2Distance_eq_dist] using
      htriangle.trans hsum
  exact ⟨{
    family := family
    family_subset_extended := hfamily_extended
    family_separated := hfamily_separated
    family_katzTao := hfamily_katzTao
    tube_cover := htube_cover
  }⟩

end Kakeya.Assouad

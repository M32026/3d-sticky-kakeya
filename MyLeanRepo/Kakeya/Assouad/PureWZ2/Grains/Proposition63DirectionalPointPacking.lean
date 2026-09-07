import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PaperDirectionPackingGeneral
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.RobustCloseCountPhase1
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.HairbrushBalancedBroadDecomposition.DirectionPacking2D
import MyLeanRepo.Kakeya.Cinematic.Section5.MaximalSeparatedCover
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.HAvgExponentArithmetic

/-!
# Pointwise quadratic direction packing for Proposition 6.3

This is the geometric counting input in the robust-transversality step.  At
one common shaded point, a `kappa`-cap is covered by
`O((kappa / rho)^2)` direction balls of radius `rho`.  Inside each such
direction ball, common incidence and paper line-essential distinctness give
an absolute bound for the possible transverse line offsets.

The two factors are deliberately kept separate: the scale-dependent factor
is two-dimensional direction packing, while the line-offset multiplicity is
an absolute constant.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open Metric Set InnerProductGeometry

attribute [local instance] Classical.propDecidable

/-- Absolute line-offset multiplicity inside one radius-`rho` direction
bucket at one common shaded point. -/
def proposition63DirectionBucketConstant : ℕ := 4801 ^ 5

/-- The dimensional constant in the resulting quadratic cap count. -/
def proposition63DirectionalPointPackingConstant : ℕ :=
  1200 * proposition63DirectionBucketConstant

/-- Multiplicity threshold used by the Proposition 6.3 Property-(P)
selection.  Its scale-dependent part has the correct quadratic direction-cap
growth. -/
def proposition63DirectionalMultiplicity (sigma loss scale : ℝ) : ℕ :=
  let epsilon₁ := (sigma - 2 * loss) / 20
  let K := Nat.ceil (Real.rpow scale (-2 * epsilon₁))
  12 * max (2 * 4 * 601 ^ 3 * 12001 ^ 3)
    (proposition63DirectionalPointPackingConstant * K ^ 2) + 12

/-- The quadratic multiplicity threshold remains absorbable in the
high-multiplicity averaging argument. -/
lemma proposition63_directional_multiplicity_exponent_arithmetic
    (sigma loss : ℝ)
    (hsigma : 0 < sigma)
    (hloss : 0 < loss)
    (hlossQuarter : loss < sigma / 4) :
    ∃ scale0 : ℝ, 0 < scale0 ∧ scale0 ≤ 1 ∧
      ∀ scale : ℝ, 0 < scale → scale ≤ scale0 →
        (proposition63DirectionalMultiplicity sigma loss scale : ℝ) *
            Real.rpow scale (sigma - 3 * loss) <
          1 / 8 := by
  let epsilon₁ : ℝ := (sigma - 2 * loss) / 20
  have hepsilon₁ : 0 < epsilon₁ := by
    dsimp only [epsilon₁]
    linarith
  let exponent : ℝ := sigma - 3 * loss - 4 * epsilon₁
  have hexponent : 0 < exponent := by
    dsimp only [exponent, epsilon₁]
    linarith
  let lineConstant : ℝ := (2 * 4 * 601 ^ 3 * 12001 ^ 3 : ℕ)
  let directionConstant : ℝ := proposition63DirectionalPointPackingConstant
  let fixedConstant : ℝ :=
    12 * (lineConstant + 4 * directionConstant) + 12
  have hfixedPositive : 0 < fixedConstant := by
    dsimp only [fixedConstant, lineConstant, directionConstant,
      proposition63DirectionalPointPackingConstant,
      proposition63DirectionBucketConstant]
    positivity
  let rawScale : ℝ := Real.rpow (1 / (16 * fixedConstant)) exponent⁻¹
  have hrawScale : 0 < rawScale := by
    dsimp only [rawScale]
    exact Real.rpow_pos_of_pos (by positivity) _
  let scale0 : ℝ := min (1 / 2) rawScale
  have hscale0 : 0 < scale0 := lt_min (by norm_num) hrawScale
  have hscale0One : scale0 ≤ 1 :=
    (min_le_left _ _).trans (by norm_num)
  refine ⟨scale0, hscale0, hscale0One, ?_⟩
  intro scale hscale hscaleBound
  have hscaleHalf : scale ≤ 1 / 2 :=
    hscaleBound.trans (min_le_left _ _)
  have hscaleOne : scale < 1 := hscaleHalf.trans_lt (by norm_num)
  let K : ℕ := Nat.ceil (Real.rpow scale (-2 * epsilon₁))
  have hpowerOne : 1 < Real.rpow scale (-2 * epsilon₁) :=
    rpow_ge_one_of_le_one' hscale hscaleOne (by linarith)
  have hKBound : (K : ℝ) ≤
      2 * Real.rpow scale (-2 * epsilon₁) := by
    have hceil : (K : ℝ) <
        Real.rpow scale (-2 * epsilon₁) + 1 := by
      dsimp only [K]
      exact Nat.ceil_lt_add_one (Real.rpow_nonneg hscale.le _)
    linarith
  have hKSquared : ((K ^ 2 : ℕ) : ℝ) ≤
      4 * Real.rpow scale (-4 * epsilon₁) := by
    have hsquare : (K : ℝ) ^ 2 ≤
        (2 * Real.rpow scale (-2 * epsilon₁)) ^ 2 := by
      gcongr
    have hpower :
        Real.rpow scale (-2 * epsilon₁) ^ 2 =
          Real.rpow scale (-4 * epsilon₁) := by
      calc
        Real.rpow scale (-2 * epsilon₁) ^ 2 =
            Real.rpow scale (-2 * epsilon₁) *
              Real.rpow scale (-2 * epsilon₁) := by ring
        _ = Real.rpow scale ((-2 * epsilon₁) + (-2 * epsilon₁)) :=
          (Real.rpow_add hscale _ _).symm
        _ = Real.rpow scale (-4 * epsilon₁) := by congr 1 <;> ring
    have hsquare' : (K : ℝ) ^ 2 ≤
        4 * Real.rpow scale (-4 * epsilon₁) := by
      calc
        (K : ℝ) ^ 2 ≤
            (2 * Real.rpow scale (-2 * epsilon₁)) ^ 2 := hsquare
        _ = 4 * Real.rpow scale (-4 * epsilon₁) := by
          rw [mul_pow, hpower]
          norm_num
    simpa only [Nat.cast_pow, Nat.cast_ofNat, mul_comm] using hsquare'
  have hpowerFourOne : 1 ≤ Real.rpow scale (-4 * epsilon₁) := by
    exact (rpow_ge_one_of_le_one' hscale hscaleOne (by linarith)).le
  have hmBound :
      (proposition63DirectionalMultiplicity sigma loss scale : ℝ) ≤
        fixedConstant * Real.rpow scale (-4 * epsilon₁) := by
    have hnat : proposition63DirectionalMultiplicity sigma loss scale ≤
        12 * ((2 * 4 * 601 ^ 3 * 12001 ^ 3) +
          proposition63DirectionalPointPackingConstant * K ^ 2) + 12 := by
      dsimp only [proposition63DirectionalMultiplicity, K, epsilon₁]
      omega
    have hreal :
        (proposition63DirectionalMultiplicity sigma loss scale : ℝ) ≤
          12 * (lineConstant + directionConstant * (K : ℝ) ^ 2) + 12 := by
      have hcast :
          ((proposition63DirectionalMultiplicity sigma loss scale : ℕ) : ℝ) ≤
            ((12 * ((2 * 4 * 601 ^ 3 * 12001 ^ 3) +
              proposition63DirectionalPointPackingConstant * K ^ 2) + 12 : ℕ) : ℝ) :=
        Nat.cast_le.mpr hnat
      calc
        (proposition63DirectionalMultiplicity sigma loss scale : ℝ) ≤
            ((12 * ((2 * 4 * 601 ^ 3 * 12001 ^ 3) +
              proposition63DirectionalPointPackingConstant * K ^ 2) +
              12 : ℕ) : ℝ) := hcast
        _ = 12 * (lineConstant + directionConstant * (K : ℝ) ^ 2) +
              12 := by
          push_cast
          rfl
    have hKSquared' : (K : ℝ) ^ 2 ≤
        4 * Real.rpow scale (-4 * epsilon₁) := by
      simpa using hKSquared
    calc
      (proposition63DirectionalMultiplicity sigma loss scale : ℝ)
          ≤ 12 * (lineConstant + directionConstant * (K : ℝ) ^ 2) + 12 :=
        hreal
      _ ≤ 12 * (lineConstant +
            directionConstant *
              (4 * Real.rpow scale (-4 * epsilon₁))) + 12 := by
        gcongr
      _ ≤ fixedConstant * Real.rpow scale (-4 * epsilon₁) := by
        dsimp only [fixedConstant]
        have hlineNonnegative : 0 ≤ lineConstant := by positivity
        have hdirectionNonnegative : 0 ≤ directionConstant := by positivity
        nlinarith
  have hpowerCombine :
      Real.rpow scale (-4 * epsilon₁) *
          Real.rpow scale (sigma - 3 * loss) =
        Real.rpow scale exponent := by
    calc
      Real.rpow scale (-4 * epsilon₁) *
          Real.rpow scale (sigma - 3 * loss) =
        Real.rpow scale ((-4 * epsilon₁) + (sigma - 3 * loss)) :=
          (Real.rpow_add hscale _ _).symm
      _ = Real.rpow scale exponent := by
        congr 1
        dsimp only [exponent]
        ring
  have hproduct :
      (proposition63DirectionalMultiplicity sigma loss scale : ℝ) *
          Real.rpow scale (sigma - 3 * loss) ≤
        fixedConstant * Real.rpow scale exponent := by
    calc
      (proposition63DirectionalMultiplicity sigma loss scale : ℝ) *
            Real.rpow scale (sigma - 3 * loss)
          ≤ (fixedConstant * Real.rpow scale (-4 * epsilon₁)) *
              Real.rpow scale (sigma - 3 * loss) := by
        gcongr
        exact Real.rpow_nonneg hscale.le _
      _ = fixedConstant * Real.rpow scale exponent := by
        rw [mul_assoc, hpowerCombine]
  have hscaleRaw : scale ≤ rawScale :=
    hscaleBound.trans (min_le_right _ _)
  have hrawPower : Real.rpow rawScale exponent =
      1 / (16 * fixedConstant) := by
    have hbaseNonnegative : 0 ≤ 1 / (16 * fixedConstant) := by positivity
    have hinverse : exponent⁻¹ * exponent = 1 := by
      field_simp [hexponent.ne']
    calc
      Real.rpow rawScale exponent =
          Real.rpow (1 / (16 * fixedConstant))
            (exponent⁻¹ * exponent) := by
        dsimp only [rawScale]
        exact (Real.rpow_mul hbaseNonnegative exponent⁻¹ exponent).symm
      _ = Real.rpow (1 / (16 * fixedConstant)) 1 := by rw [hinverse]
      _ = 1 / (16 * fixedConstant) := Real.rpow_one _
  have hscalePower : Real.rpow scale exponent ≤
      1 / (16 * fixedConstant) := by
    calc
      Real.rpow scale exponent ≤ Real.rpow rawScale exponent :=
        Real.rpow_le_rpow hscale.le hscaleRaw hexponent.le
      _ = 1 / (16 * fixedConstant) := hrawPower
  have hfixedBound : fixedConstant * Real.rpow scale exponent ≤ 1 / 16 := by
    calc
      fixedConstant * Real.rpow scale exponent
          ≤ fixedConstant * (1 / (16 * fixedConstant)) := by gcongr
      _ = 1 / 16 := by field_simp [hfixedPositive.ne']
  exact hproduct.trans_lt (hfixedBound.trans_lt (by norm_num))

/-- Pointwise close-direction counts decrease under a subshading. -/
lemma proposition63_close_direction_count_transfer
    {rho : ℝ}
    {family : Kakeya.Streamlined.TubeFamily rho}
    {smaller larger : WZ1PaperTubeShading family}
    (hsub : PaperIsSubshading smaller larger)
    (point : Point3) (index : Fin family.card) (kappa : ℝ) :
    paperCloseDirectionCount smaller point index kappa ≤
      paperCloseDirectionCount larger point index kappa := by
  classical
  apply Finset.card_le_card
  intro other hother
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hother ⊢
  exact ⟨hsub other hother.1, hother.2⟩

/-- A small projective cross-product cap lies in an ordinary cap after the
paper directions are oriented into the positive vertical chart. -/
lemma paper_acute_angle_le_two_mul_of_cross_lt
    {rho kappa : ℝ}
    (hkappa : 0 < kappa) (hkappaHalf : kappa ≤ 1 / 2)
    {first second : Kakeya.DeltaTube rho}
    (hfirst : WZ1PaperTubeInLineClass first)
    (hsecond : WZ1PaperTubeInLineClass second)
    (hcross : ‖wz1Cross first.direction second.direction‖ < kappa) :
    hairbrushAcuteDirectionAngle
        (wz1PaperDirection first) (wz1PaperDirection second) ≤
      2 * kappa := by
  let u := wz1PaperDirection first
  let v := wz1PaperDirection second
  have hu : ‖u‖ = 1 := wz1PaperDirection_norm first
  have hv : ‖v‖ = 1 := wz1PaperDirection_norm second
  rcases paperDirection_sign first with ⟨s1, hs1, hdir1⟩
  rcases paperDirection_sign second with ⟨s2, hs2, hdir2⟩
  have hraw :
      ‖wz1Cross first.direction second.direction‖ =
        ‖wz1Cross u v‖ := by
    rw [hdir1, hdir2]
    exact crossNorm_sign_invariant u v s1 s2 hs1 hs2
  have hcrossPaper : ‖wz1Cross u v‖ < kappa := by
    rw [← hraw]
    exact hcross
  have hinnerSq : (inner ℝ u v) ^ 2 > 1 - kappa ^ 2 := by
    have hidentity :
        ‖wz1Cross u v‖ ^ 2 = 1 - (inner ℝ u v) ^ 2 :=
      cross_norm_sq u v hu hv
    have hcrossSq : ‖wz1Cross u v‖ ^ 2 < kappa ^ 2 := by
      gcongr
    linarith
  have hinnerLower : -(1 / 2 : ℝ) ≤ inner ℝ u v :=
    paper_inner_lower_bound hu hv hfirst.1 hsecond.1
  have hinner : inner ℝ u v > 1 - kappa ^ 2 :=
    paper_inner_strict_lower_general hkappa hkappaHalf hinnerSq hinnerLower
  have hinnerNonnegative : 0 ≤ inner ℝ u v := by
    have hkappaSq : kappa ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by gcongr
    nlinarith
  have hangleEq :
      angle u v = Real.arccos (inner ℝ u v) := by
    unfold angle
    rw [hu, hv]
    norm_num
  have hangleHalf : angle u v ≤ Real.pi / 2 := by
    rw [hangleEq]
    exact Real.arccos_le_pi_div_two.mpr hinnerNonnegative
  have hangleNonnegative : 0 ≤ angle u v := angle_nonneg u v
  have hangleSin : angle u v ≤ (Real.pi / 2) * Real.sin (angle u v) :=
    le_pi2_mul_sin (angle u v) hangleNonnegative hangleHalf
  have hcrossAngle : ‖wz1Cross u v‖ = Real.sin (angle u v) :=
    crossNorm_eq_sin_angle hu hv
  have hangleKappa : angle u v ≤ 2 * kappa := by
    calc
      angle u v ≤ (Real.pi / 2) * Real.sin (angle u v) := hangleSin
      _ = (Real.pi / 2) * ‖wz1Cross u v‖ := by rw [hcrossAngle]
      _ ≤ (Real.pi / 2) * kappa := by
        gcongr
      _ ≤ 2 * kappa := by
        have hpi : Real.pi ≤ 4 := Real.pi_le_four
        nlinarith
  have hacute : hairbrushAcuteDirectionAngle u v ≤ angle u v := by
    dsimp only [hairbrushAcuteDirectionAngle]
    rw [hangleEq]
    exact min_le_left _ _
  exact hacute.trans hangleKappa

/-- Paper directions in one Euclidean `rho`-ball and through one shaded
point have bounded line-metric multiplicity. -/
lemma proposition63_direction_bucket_cardinality
    {rho : ℝ}
    {family : Kakeya.Streamlined.TubeFamily rho}
    {shading : WZ1PaperTubeShading family}
    (hdistinct : WZ1PaperIsEssentiallyDistinct family)
    (hline : WZ1PaperIsLineClass family)
    (hrho : 0 < rho) (hrhoSmall : rho ≤ 1 / 10000)
    (point : Point3)
    (indices : Finset (Fin family.card))
    (hactive : ∀ index ∈ indices, point ∈ shading.carrier index)
    (center : Point3)
    (hcenter : ∃ reference ∈ indices,
      wz1PaperDirection (family.tube reference) = center)
    (hcap : ∀ index ∈ indices,
      dist (wz1PaperDirection (family.tube index)) center ≤ rho) :
    indices.card ≤ proposition63DirectionBucketConstant := by
  rcases hcenter with ⟨reference, hreference, hreferenceDirection⟩
  let surrounding : Finset (Fin family.card) :=
    Finset.univ.filter fun index =>
      wz1PaperLineDistance
          (family.tube index) (family.tube reference) ≤
        300 * rho
  have hindicesSubset : indices ⊆ surrounding := by
    intro index hindex
    have hdirectionDist :
        dist (wz1PaperDirection (family.tube reference))
            (wz1PaperDirection (family.tube index)) ≤ rho := by
      rw [hreferenceDirection, dist_comm]
      exact hcap index hindex
    have hpaperCross :
        ‖wz1Cross
            (wz1PaperDirection (family.tube reference))
            (wz1PaperDirection (family.tube index))‖ ≤ rho := by
      have hrewrite :
          wz1Cross
              (wz1PaperDirection (family.tube reference))
              (wz1PaperDirection (family.tube index)) =
            wz1Cross
              (wz1PaperDirection (family.tube reference) -
                wz1PaperDirection (family.tube index))
              (wz1PaperDirection (family.tube index)) := by
        rw [sub_eq_add_neg, wz1Cross_add_left]
        have hneg :
            wz1Cross (-(wz1PaperDirection (family.tube index)))
                (wz1PaperDirection (family.tube index)) = 0 := by
          simp [wz1Cross, crossProduct] <;> ring <;> trivial
        rw [hneg, add_zero]
      rw [hrewrite]
      calc
        ‖wz1Cross
            (wz1PaperDirection (family.tube reference) -
              wz1PaperDirection (family.tube index))
            (wz1PaperDirection (family.tube index))‖
            ≤ ‖wz1PaperDirection (family.tube reference) -
                wz1PaperDirection (family.tube index)‖ *
              ‖wz1PaperDirection (family.tube index)‖ :=
          wz1Cross_norm_le _ _
        _ = dist (wz1PaperDirection (family.tube reference))
              (wz1PaperDirection (family.tube index)) := by
          rw [wz1PaperDirection_norm]
          simp [dist_eq_norm]
        _ ≤ rho := hdirectionDist
    rcases paperDirection_sign (family.tube reference) with
      ⟨s1, hs1, hdir1⟩
    rcases paperDirection_sign (family.tube index) with
      ⟨s2, hs2, hdir2⟩
    have hrawCross :
        ‖wz1Cross (family.tube reference).direction
            (family.tube index).direction‖ =
          ‖wz1Cross
            (wz1PaperDirection (family.tube reference))
            (wz1PaperDirection (family.tube index))‖ := by
      rw [hdir1, hdir2]
      exact crossNorm_sign_invariant _ _ s1 s2 hs1 hs2
    have hcrossThree :
        ‖wz1Cross (family.tube reference).direction
            (family.tube index).direction‖ < 3 * rho := by
      rw [hrawCross]
      linarith
    have hlineDistance :
        wz1PaperLineDistance
            (family.tube index) (family.tube reference) ≤
          300 * rho := by
      simpa only [show (100 : ℝ) * 3 * rho = 300 * rho by ring] using
        paper_line_distance_shared_point_general
          hrho hrhoSmall (show (1 : ℝ) ≤ 3 by norm_num)
          (show (3 : ℝ) * rho ≤ 1 / 2 by
            calc
              (3 : ℝ) * rho ≤ 3 * (1 / 10000 : ℝ) := by gcongr
              _ ≤ 1 / 2 := by norm_num)
          (hline reference) (hline index) point
          (shading.subset_body reference
            (hactive reference hreference))
          (shading.subset_body index (hactive index hindex))
          hcrossThree
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlineDistance⟩
  have hsurrounding :
      surrounding.card ≤ (2 * Nat.ceil (8 * (300 * rho) / rho) + 1) ^ 5 :=
    tube_packing_bound_general hdistinct hline hrho
      (300 * rho) (by positivity) reference
  have hratio : 8 * (300 * rho) / rho = 2400 := by
    field_simp [hrho.ne']
    ring
  have hsurrounding' :
      surrounding.card ≤ proposition63DirectionBucketConstant := by
    rw [hratio] at hsurrounding
    norm_num [proposition63DirectionBucketConstant] at hsurrounding ⊢
    exact hsurrounding
  exact (Finset.card_le_card hindicesSubset).trans hsurrounding'

/-- Quadratic pointwise count in a `K * rho` projective direction cap. -/
lemma proposition63_close_direction_count_quadratic
    {rho : ℝ} {K : ℕ}
    {family : Kakeya.Streamlined.TubeFamily rho}
    {shading : WZ1PaperTubeShading family}
    (hdistinct : WZ1PaperIsEssentiallyDistinct family)
    (hline : WZ1PaperIsLineClass family)
    (hrho : 0 < rho) (hrhoSmall : rho ≤ 1 / 10000)
    (hK : 1 ≤ K) (hKScale : (K : ℝ) * rho ≤ 1 / 2)
    (point : Point3) (index : Fin family.card)
    (hpoint : point ∈ shading.carrier index) :
    paperCloseDirectionCount shading point index ((K : ℝ) * rho) ≤
      proposition63DirectionalPointPackingConstant * K ^ 2 := by
  classical
  let close : Finset (Fin family.card) :=
    Finset.univ.filter fun other =>
      point ∈ shading.carrier other ∧
        ‖wz1Cross (family.tube index).direction
          (family.tube other).direction‖ < (K : ℝ) * rho
  let direction : Fin family.card → Point3 := fun other =>
    wz1PaperDirection (family.tube other)
  let directionSet : Finset Point3 := close.image direction
  rcases Kakeya.Cinematic.exists_maximal_separated_cover
      (S := directionSet) hrho with
    ⟨centers, hcentersSubset, hcentersSeparated, hcentersCover⟩
  have hcentersUnit : ∀ center ∈ centers, ‖center‖ = 1 := by
    intro center hcenter
    rcases Finset.mem_image.mp
        (hcentersSubset hcenter) with ⟨other, _hother, rfl⟩
    exact wz1PaperDirection_norm _
  have hcentersSeparated' : ∀ first ∈ centers, ∀ second ∈ centers,
      first ≠ second → 2 * rho / Real.pi ≤ dist first second := by
    intro first hfirst second hsecond hne
    have hsep := hcentersSeparated first hfirst second hsecond hne
    have hcoeff : 2 * rho / Real.pi ≤ rho := by
      apply (div_le_iff₀ Real.pi_pos).2
      nlinarith [Real.pi_gt_three]
    exact hcoeff.trans hsep.le
  have hrhoOne : rho ≤ 1 := hrhoSmall.trans (by norm_num)
  have hrhoKappa : rho ≤ 2 * ((K : ℝ) * rho) := by
    have hKReal : (1 : ℝ) ≤ K := by exact_mod_cast hK
    nlinarith
  have hthetaOne : 2 * ((K : ℝ) * rho) ≤ 1 := by linarith
  have hcentersCap : ∀ center ∈ centers,
      hairbrushAcuteDirectionAngle center
          (wz1PaperDirection (family.tube index)) ≤
        2 * ((K : ℝ) * rho) := by
    intro center hcenter
    rcases Finset.mem_image.mp (hcentersSubset hcenter) with
      ⟨other, hother, rfl⟩
    have hclose := (Finset.mem_filter.mp hother).2.2
    have hcap := paper_acute_angle_le_two_mul_of_cross_lt
      (by positivity) hKScale (hline index) (hline other) hclose
    simpa [hairbrushAcuteDirectionAngle, real_inner_comm] using hcap
  have hcentersReal :
      (centers.card : ℝ) ≤
        300 * ((2 * ((K : ℝ) * rho)) / rho) ^ 2 :=
    direction_cap_packing_2d hrho hrhoOne hrhoKappa hthetaOne
      hcentersUnit hcentersSeparated'
      (wz1PaperDirection (family.tube index))
      (wz1PaperDirection_norm _) hcentersCap
  have hcentersReal' :
      (centers.card : ℝ) ≤ 1200 * (K : ℝ) ^ 2 := by
    calc
      (centers.card : ℝ)
          ≤ 300 * ((2 * ((K : ℝ) * rho)) / rho) ^ 2 :=
        hcentersReal
      _ = 1200 * (K : ℝ) ^ 2 := by
        field_simp [hrho.ne']
        ring
  have hcentersNat : centers.card ≤ 1200 * K ^ 2 := by
    exact_mod_cast hcentersReal'
  let bucket : Point3 → Finset (Fin family.card) := fun center =>
    close.filter fun other => dist (direction other) center ≤ rho
  have hbucketCard : ∀ center ∈ centers,
      (bucket center).card ≤ proposition63DirectionBucketConstant := by
    intro center hcenter
    apply proposition63_direction_bucket_cardinality
      hdistinct hline hrho hrhoSmall point (bucket center)
    · intro other hother
      exact (Finset.mem_filter.mp
        (Finset.mem_filter.mp hother).1).2.1
    · rcases Finset.mem_image.mp (hcentersSubset hcenter) with
        ⟨reference, hreference, hreferenceDirection⟩
      refine ⟨reference, ?_, hreferenceDirection⟩
      exact Finset.mem_filter.mpr
        ⟨hreference, by simpa [direction, hreferenceDirection] using hrho.le⟩
    · intro other hother
      exact (Finset.mem_filter.mp hother).2
  have hcloseCover : close ⊆ centers.biUnion bucket := by
    intro other hother
    have hdirection : direction other ∈ directionSet :=
      Finset.mem_image.mpr ⟨other, hother, rfl⟩
    rcases hcentersCover (direction other) hdirection with
      ⟨center, hcenter, hdistance⟩
    exact Finset.mem_biUnion.mpr
      ⟨center, hcenter, Finset.mem_filter.mpr ⟨hother, hdistance⟩⟩
  have hcloseCard :
      close.card ≤ centers.card * proposition63DirectionBucketConstant := by
    calc
      close.card ≤ (centers.biUnion bucket).card :=
        Finset.card_le_card hcloseCover
      _ ≤ ∑ center ∈ centers, (bucket center).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _center ∈ centers, proposition63DirectionBucketConstant :=
        Finset.sum_le_sum fun center hcenter => hbucketCard center hcenter
      _ = centers.card * proposition63DirectionBucketConstant := by
        simp [Finset.sum_const]
  have hfinal :
      close.card ≤ proposition63DirectionalPointPackingConstant * K ^ 2 := by
    calc
      close.card ≤ centers.card * proposition63DirectionBucketConstant :=
        hcloseCard
      _ ≤ (1200 * K ^ 2) * proposition63DirectionBucketConstant := by
        exact Nat.mul_le_mul_right proposition63DirectionBucketConstant
          hcentersNat
      _ = proposition63DirectionalPointPackingConstant * K ^ 2 := by
        simp [proposition63DirectionalPointPackingConstant]
        ring
  change close.card ≤ proposition63DirectionalPointPackingConstant * K ^ 2
  exact hfinal

end Kakeya.Assouad.PureWZ2

end

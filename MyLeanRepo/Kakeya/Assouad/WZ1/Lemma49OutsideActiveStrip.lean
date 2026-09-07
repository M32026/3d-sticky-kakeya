import MyLeanRepo.Kakeya.Assouad.ConstantAbsorption
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma49OutsideActiveStripCore
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma49OutsideActiveStripStatements

/-!
# Outside-active-strip branch of WZ1 Lemma 49

One graph-active first-coordinate vertex outside the enlarged orthogonal
strip supplies a large dot component in the strip direction.  Uniform
tripartite density selects a dense active `G₁` fiber through that vertex.
The active common-width definition puts every point of that fiber in the
same width-`t` strip.  The closed packing core then gives the long
dot-difference projection.

No unused ambient vertex is included in the strip-width maximum.
-/

namespace Kakeya.Assouad

noncomputable section

open scoped ENNReal

/--
The three small-scale inequalities used by the direct outside-strip branch:
fixed-constant absorption, the factor-twenty separation margin, and the
radius budget.
-/
private structure WZ1Lemma49OutsideThreshold
    (delta epsilon eta epsilonHalf : ℝ) where
  constant :
    (16 / 5 : ℝ) ^ (1 - epsilon) * 32 ^ epsilon ≤
      Real.rpow delta (2 * eta - epsilonHalf * epsilon)
  twenty : 20 ≤ Real.rpow delta (-epsilonHalf)
  radius :
    Real.rpow delta (epsilonHalf - eta) ≤ 2 / 5

/-- Simultaneously absorb all fixed constants in the direct branch. -/
private theorem wz1Lemma49_exists_outside_threshold
    (epsilon eta epsilonHalf : ℝ)
    (hepsilon : 0 < epsilon)
    (heta : 0 < eta)
    (hepsilonHalf : 0 < epsilonHalf)
    (hexponent : 2 * eta < epsilonHalf * epsilon)
    (hradiusGap : 0 < epsilonHalf - eta) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        WZ1Lemma49OutsideThreshold
          delta epsilon eta epsilonHalf := by
  let fixedConstant : ℝ :=
    (16 / 5 : ℝ) ^ (1 - epsilon) * 32 ^ epsilon
  rcases
      exists_delta_mul_rpow_le_rpow
        fixedConstant (by positivity)
        (alpha := 0)
        (beta := 2 * eta - epsilonHalf * epsilon)
        (by linarith) with
    ⟨constantScale, hconstantScale,
      hconstantScaleOne, hconstant⟩
  rcases
      exists_delta_mul_rpow_le_rpow
        20 (by norm_num)
        (alpha := 0) (beta := -epsilonHalf)
        (by linarith) with
    ⟨twentyScale, htwentyScale,
      htwentyScaleOne, htwenty⟩
  rcases
      exists_delta_mul_rpow_le_rpow
        (5 / 2 : ℝ) (by norm_num)
        (alpha := epsilonHalf - eta) (beta := 0)
        (by linarith) with
    ⟨radiusScale, hradiusScale,
      hradiusScaleOne, hradius⟩
  let delta₀ := min constantScale (min twentyScale radiusScale)
  have hdelta₀ : 0 < delta₀ := by
    simp [delta₀, hconstantScale, htwentyScale, hradiusScale]
  have hdelta₀One : delta₀ ≤ 1 :=
    (min_le_left constantScale _).trans hconstantScaleOne
  refine ⟨delta₀, hdelta₀, hdelta₀One, ?_⟩
  intro delta hdelta hdeltaSmall
  have hdeltaConstant : delta ≤ constantScale :=
    hdeltaSmall.trans (min_le_left _ _)
  have hdeltaTwenty : delta ≤ twentyScale :=
    hdeltaSmall.trans
      ((min_le_right constantScale _).trans
        (min_le_left _ _))
  have hdeltaRadius : delta ≤ radiusScale :=
    hdeltaSmall.trans
      ((min_le_right constantScale _).trans
        (min_le_right _ _))
  have hconstantRaw :=
    hconstant delta hdelta hdeltaConstant
  have htwentyRaw :=
    htwenty delta hdelta hdeltaTwenty
  have hradiusRaw :=
    hradius delta hdelta hdeltaRadius
  have hconstantFinal :
      fixedConstant ≤
        Real.rpow delta
          (2 * eta - epsilonHalf * epsilon) := by
    simpa [Real.rpow_zero, fixedConstant] using hconstantRaw
  have htwentyFinal :
      20 ≤ Real.rpow delta (-epsilonHalf) := by
    simpa [Real.rpow_zero] using htwentyRaw
  have hradiusFinal :
      Real.rpow delta (epsilonHalf - eta) ≤ 2 / 5 := by
    have hraw :
        (5 / 2 : ℝ) *
            Real.rpow delta (epsilonHalf - eta) ≤ 1 := by
      simpa [Real.rpow_zero] using hradiusRaw
    linarith
  exact
    { constant := hconstantFinal
      twenty := htwentyFinal
      radius := hradiusFinal }

/--
One escaping graph-active first vertex gives the long-projection alternative
of WZ1 Lemma 49.
-/
theorem wz1_lemma49_outside_active_strip :
    WZ1Lemma49OutsideActiveStripStatement := by
  classical
  intro epsilon hepsilon hepsilonOne
  let eta := epsilon ^ 3 / 400
  let epsilonHalf := wz1Lemma49AuxiliaryEpsilon epsilon
  have heta : 0 < eta := by
    dsimp only [eta]
    positivity
  have hetaBudget : eta ≤ epsilon ^ 2 / 100 := by
    dsimp only [eta]
    have hepsilonLe : epsilon ≤ 1 := hepsilonOne.le
    have hepsilonSq : 0 < epsilon ^ 2 := sq_pos_of_pos hepsilon
    nlinarith [mul_le_mul_of_nonneg_left hepsilonLe hepsilonSq.le]
  have hepsilonHalf : 0 < epsilonHalf := by
    dsimp only [epsilonHalf, wz1Lemma49AuxiliaryEpsilon]
    positivity
  have hexponent :
      2 * eta < epsilonHalf * epsilon := by
    dsimp only [eta, epsilonHalf, wz1Lemma49AuxiliaryEpsilon]
    nlinarith [sq_pos_of_pos hepsilon]
  have hradiusGap : 0 < epsilonHalf - eta := by
    dsimp only [eta, epsilonHalf, wz1Lemma49AuxiliaryEpsilon]
    have hepsilonSq : 0 < epsilon ^ 2 := sq_pos_of_pos hepsilon
    have hepsilonLe : epsilon < 4 := hepsilonOne.trans (by norm_num)
    nlinarith [mul_lt_mul_of_pos_left hepsilonLe hepsilonSq]
  rcases
      wz1Lemma49_exists_outside_threshold
        epsilon eta epsilonHalf hepsilon heta
        hepsilonHalf hexponent hradiusGap with
    ⟨delta₀, hdelta₀, hdelta₀One, hthreshold⟩
  refine
    ⟨eta, delta₀, heta, hetaBudget,
      hdelta₀, hdelta₀One, ?_⟩
  intro delta hdelta hdeltaSmall
  have hdeltaOne : delta ≤ 1 :=
    hdeltaSmall.trans hdelta₀One
  have hsmall :=
    hthreshold delta hdelta hdeltaSmall
  intro F G₁ G₂ hFNonempty hG₁Nonempty hG₂Nonempty
    hFBall hG₁Ball hG₂Ball
    hFSeparated hG₁Separated hG₂Separated
    hFFrostman hG₁Frostman hG₂Frostman
    hstandard H hDensity base direction hdirection
  let t :=
    wz1ActiveCommonWidth
      delta H hDensity.1 base direction
  change
    (∃ edge ∈ H,
      edge.1 ∉
        wz1LineNeighborhood 0
          (wz1Perp2 direction)
          (Real.rpow delta
            (-wz1Lemma49AuxiliaryEpsilon epsilon) * t)) →
      WZ1StripLocalizationLongProjection
        delta epsilon eta H
  intro hescape
  rcases hescape with ⟨sourceEdge, hsourceEdge, hsourceOutside⟩
  let first := sourceEdge.1
  have hfirstF : first ∈ F := by
    let encoded := wz1TripleCoordinate sourceEdge
    have hencoded :
        encoded ∈ wz1EncodeTriples H :=
      Finset.mem_image.mpr
        ⟨sourceEdge, hsourceEdge, rfl⟩
    have hsupported := hDensity.2.1 encoded hencoded 0
    simpa [first, encoded, wz1TripleCoordinate,
      wz1TripleVertexClasses] using hsupported
  let R := |inner ℝ first direction|
  have hperpPerp :
      wz1Perp2 (wz1Perp2 direction) = -direction := by
    ext i
    fin_cases i <;> simp [wz1Perp2]
  have hROutside :
      Real.rpow delta (-epsilonHalf) * t < R := by
    change
      ¬|inner ℝ (first - 0)
          (wz1Perp2 (wz1Perp2 direction))| ≤
        Real.rpow delta
          (-wz1Lemma49AuxiliaryEpsilon epsilon) * t at hsourceOutside
    rw [hperpPerp, sub_zero, inner_neg_right,
      abs_neg] at hsourceOutside
    simpa [R, epsilonHalf] using
      (lt_of_not_ge hsourceOutside)
  have hfirstNorm : ‖first‖ ≤ 1 := by
    have h := hFBall first hfirstF
    simpa [dist_zero_right] using h
  have hROne : R ≤ 1 := by
    calc
      R = |inner ℝ first direction| := rfl
      _ ≤ ‖first‖ * ‖direction‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ 1 := by rw [hdirection, mul_one]; exact hfirstNorm
  have hdeltaT : delta ≤ t :=
    wz1Lemma49_delta_le_activeCommonWidth
      hDensity.1 base direction
  have ht : 0 < t := hdelta.trans_le hdeltaT
  have hR : 0 < R := by
    exact (mul_pos
      (Real.rpow_pos_of_pos hdelta _) ht).trans hROutside
  have hRTwenty : 20 * t ≤ R := by
    calc
      20 * t ≤ Real.rpow delta (-epsilonHalf) * t := by
        gcongr
        exact hsmall.twenty
      _ ≤ R := hROutside.le
  have htOne : t ≤ 1 := by
    have hone :
        1 ≤ Real.rpow delta (-epsilonHalf) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos
        hdelta hdeltaOne (by linarith)
    have htR :
        t ≤ Real.rpow delta (-epsilonHalf) * t := by
      nlinarith
    exact htR.trans (hROutside.le.trans hROne)
  have hRLower :
      (1 / 4 : ℝ) *
          Real.rpow delta (-epsilonHalf) * t ≤ R := by
    have hfactor :
        (1 / 4 : ℝ) *
            Real.rpow delta (-epsilonHalf) * t ≤
          Real.rpow delta (-epsilonHalf) * t := by
      have hproduct :
          0 ≤ Real.rpow delta (-epsilonHalf) * t :=
        (mul_pos
          (Real.rpow_pos_of_pos hdelta (-epsilonHalf)) ht).le
      calc
        (1 / 4 : ℝ) *
              Real.rpow delta (-epsilonHalf) * t =
            (1 / 4 : ℝ) *
              (Real.rpow delta (-epsilonHalf) * t) := by ring
        _ ≤ 1 * (Real.rpow delta (-epsilonHalf) * t) := by
          gcongr
          norm_num
        _ = Real.rpow delta (-epsilonHalf) * t := by ring
    exact hfactor.trans hROutside.le
  have hseparationScale : 8 * t / R ≤ 1 := by
    exact (div_le_one hR).mpr (by linarith [hRTwenty])
  have hradius :
      Real.rpow delta (-eta) * t ≤ 2 * (R / 5) := by
    have hdecompose :
        Real.rpow delta (-eta) =
          Real.rpow delta (-epsilonHalf) *
            Real.rpow delta (epsilonHalf - eta) := by
      calc
        Real.rpow delta (-eta) =
            Real.rpow delta
              ((-epsilonHalf) + (epsilonHalf - eta)) := by
          congr 1
          ring
        _ =
            Real.rpow delta (-epsilonHalf) *
              Real.rpow delta (epsilonHalf - eta) :=
          Real.rpow_add hdelta _ _
    calc
      Real.rpow delta (-eta) * t =
          (Real.rpow delta (-epsilonHalf) *
            Real.rpow delta (epsilonHalf - eta)) * t := by
        rw [hdecompose]
      _ ≤
          (Real.rpow delta (-epsilonHalf) *
            (2 / 5 : ℝ)) * t := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            hsmall.radius
            (Real.rpow_nonneg hdelta.le _))
          ht.le
      _ =
          (2 / 5 : ℝ) *
            (Real.rpow delta (-epsilonHalf) * t) := by ring
      _ ≤ (2 / 5 : ℝ) * R := by gcongr
      _ = 2 * (R / 5) := by ring
  rcases
      wz1Lemma49_uniform_density_fiber_g1
        hDensity hfirstF
        ⟨sourceEdge, hsourceEdge, rfl⟩ with
    ⟨third, hthirdG₂, hfiberENN⟩
  let fiber : Finset Point2 :=
    G₁.filter fun second =>
      (first, second, third) ∈ H
  have hfiberSubset : fiber ⊆ G₁ := by
    intro second hsecond
    exact (Finset.mem_filter.mp hsecond).1
  have hfiberEdges :
      ∀ second ∈ fiber,
        (first, second, third) ∈ H := by
    intro second hsecond
    exact (Finset.mem_filter.mp hsecond).2
  have hfiberSize :
      Real.rpow delta eta * (G₁.card : ℝ) ≤
        (fiber.card : ℝ) := by
    have hleft :
        Kakeya.realRpowENN delta eta *
            (G₁.card : ENNReal) =
          ENNReal.ofReal
            (Real.rpow delta eta * (G₁.card : ℝ)) := by
      simp only [Kakeya.realRpowENN]
      calc
        ENNReal.ofReal (Real.rpow delta eta) *
              (G₁.card : ENNReal) =
            ENNReal.ofReal (Real.rpow delta eta) *
              ENNReal.ofReal (G₁.card : ℝ) := by
          norm_cast
        _ =
            ENNReal.ofReal
              (Real.rpow delta eta * (G₁.card : ℝ)) := by
          exact
            (ENNReal.ofReal_mul
              (Real.rpow_nonneg hdelta.le eta)).symm
    rw [hleft] at hfiberENN
    have hcast :
        (fiber.card : ENNReal) =
          ENNReal.ofReal (fiber.card : ℝ) := by
      norm_cast
    rw [hcast] at hfiberENN
    exact
      (ENNReal.ofReal_le_ofReal_iff
        (by positivity : 0 ≤ (fiber.card : ℝ))).mp hfiberENN
  have hfiberStrip :
      ∀ second ∈ fiber,
        |inner ℝ (second - base)
            (wz1Perp2 direction)| ≤ t := by
    intro second hsecond
    have hedge := hfiberEdges second hsecond
    have hmem :=
      wz1Lemma49_second_mem_activeCommonStrip
        (delta := delta) hDensity.1 base direction hedge
    exact hmem
  have hdiameter :
      ∀ second ∈ G₁, ∀ other ∈ G₁,
        dist second other ≤ 1 / 10 :=
    hstandard.2.1
  exact
    wz1_lemma49_outside_active_strip_core
      hdelta hdeltaOne hepsilon heta hepsilonHalf
      hexponent ht hdeltaT htOne hR hROne
      hRLower hRTwenty hseparationScale
      hsmall.constant hradius hdirection
      hfiberStrip hG₁Frostman hG₁Nonempty hdiameter
      hfirstNorm rfl hfiberSubset hfiberSize hfiberEdges

end

end Kakeya.Assouad

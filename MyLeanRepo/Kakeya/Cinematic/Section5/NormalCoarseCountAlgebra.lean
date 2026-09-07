import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.Algebra
import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.ClusterDefinitions
import MyLeanRepo.Kakeya.Cinematic.Section5.LevelSetInputs

/-!
# Algebra after the normal coarse rectangle count

The cluster lower scale is chosen from a common coarse support cardinality.
This module turns that choice into the `l_coarse⁻³ᐟ²` factor needed to cancel
the preceding coarse-multiplicity interpolation bound.
-/

noncomputable section

namespace Kakeya.Cinematic

lemma cluster_card_le
    (H : FiniteFunctionFamily) (center : C2Function) (radius : ℝ) :
    (H.cluster center radius).card ≤ H.card := by
  rw [FiniteFunctionFamily.card, FiniteFunctionFamily.card]
  exact Set.ncard_le_ncard Set.inter_subset_left H.finite

lemma bipartiteNormalizedCount_clusters_le
    (H : FiniteFunctionFamily)
    (leftCenter rightCenter : C2Function) (radius : ℝ)
    (q centers support : ℕ)
    (hq : 0 < q)
    (hcenters : 0 < centers)
    (hsupport : 0 < support)
    (hupper : support < 2 * centers * (q + 1)) :
    RectangleFamily.bipartiteNormalizedCount
        (H.cluster leftCenter radius)
        (H.cluster rightCenter radius) q q ≤
      8 * (centers : ℝ) * (H.card : ℝ) / (support : ℝ) := by
  have hqReal : 0 < (q : ℝ) := by
    exact_mod_cast hq
  have hcentersReal : 0 < (centers : ℝ) := by
    exact_mod_cast hcenters
  have hsupportReal : 0 < (support : ℝ) := by
    exact_mod_cast hsupport
  have hqSucc : q + 1 ≤ 2 * q := by omega
  have hsupportFour :
      support < 4 * centers * q := by
    calc
      support < 2 * centers * (q + 1) := hupper
      _ ≤ 2 * centers * (2 * q) := by
        gcongr
      _ = 4 * centers * q := by ring
  have hsupportFourReal :
      (support : ℝ) < 4 * (centers : ℝ) * (q : ℝ) := by
    exact_mod_cast hsupportFour
  have hratio :
      (H.card : ℝ) / (q : ℝ) ≤
        4 * (centers : ℝ) * (H.card : ℝ) /
          (support : ℝ) := by
    have hHNonneg : 0 ≤ (H.card : ℝ) := by positivity
    apply (div_le_div_iff₀ hqReal hsupportReal).2
    have hscale :
        (support : ℝ) * (H.card : ℝ) ≤
          (4 * (centers : ℝ) * (q : ℝ)) *
            (H.card : ℝ) :=
      mul_le_mul_of_nonneg_right hsupportFourReal.le hHNonneg
    nlinarith
  have hleft :
      ((H.cluster leftCenter radius).card : ℝ) / (q : ℝ) ≤
        (H.card : ℝ) / (q : ℝ) := by
    exact div_le_div_of_nonneg_right
      (by exact_mod_cast cluster_card_le H leftCenter radius)
      hqReal.le
  have hright :
      ((H.cluster rightCenter radius).card : ℝ) / (q : ℝ) ≤
        (H.card : ℝ) / (q : ℝ) := by
    exact div_le_div_of_nonneg_right
      (by exact_mod_cast cluster_card_le H rightCenter radius)
      hqReal.le
  unfold RectangleFamily.bipartiteNormalizedCount
  calc
    ((H.cluster leftCenter radius).card : ℝ) / (q : ℝ) +
          ((H.cluster rightCenter radius).card : ℝ) / (q : ℝ) ≤
        (H.card : ℝ) / (q : ℝ) +
          (H.card : ℝ) / (q : ℝ) :=
      add_le_add hleft hright
    _ ≤
        2 *
          (4 * (centers : ℝ) * (H.card : ℝ) /
            (support : ℝ)) := by
      nlinarith
    _ =
        8 * (centers : ℝ) * (H.card : ℝ) /
          (support : ℝ) := by ring

lemma bipartiteNormalizedCount_one_le_ambient
    (H W B : FiniteFunctionFamily)
    (hW : W.carrier ⊆ H.carrier)
    (hB : B.carrier ⊆ H.carrier) :
    RectangleFamily.bipartiteNormalizedCount W B 1 1 ≤
      2 * (H.card : ℝ) := by
  have hWcard : W.card ≤ H.card :=
    Set.ncard_le_ncard hW H.finite
  have hBcard : B.card ≤ H.card :=
    Set.ncard_le_ncard hB H.finite
  have hWreal : (W.card : ℝ) ≤ (H.card : ℝ) := by
    exact_mod_cast hWcard
  have hBreal : (B.card : ℝ) ≤ (H.card : ℝ) := by
    exact_mod_cast hBcard
  unfold RectangleFamily.bipartiteNormalizedCount
  norm_num
  linarith

lemma rpow_log_mono
    {x y : ℝ}
    (hx : 1 ≤ x) (hxy : x ≤ y) :
    Real.rpow x (3 / 2 : ℝ) * Real.log x ≤
      Real.rpow y (3 / 2 : ℝ) * Real.log y := by
  have hxPos : 0 < x := by linarith
  have hyPos : 0 < y := hxPos.trans_le hxy
  have hpow :
      Real.rpow x (3 / 2 : ℝ) ≤
        Real.rpow y (3 / 2 : ℝ) :=
    Real.rpow_le_rpow hxPos.le hxy (by norm_num)
  have hlog : Real.log x ≤ Real.log y :=
    Real.log_le_log hxPos hxy
  have hpowNonneg :
      0 ≤ Real.rpow x (3 / 2 : ℝ) :=
    Real.rpow_nonneg hxPos.le _
  have hpowYNonneg :
      0 ≤ Real.rpow y (3 / 2 : ℝ) :=
    Real.rpow_nonneg hyPos.le _
  have hlogNonneg : 0 ≤ Real.log x :=
    Real.log_nonneg hx
  exact mul_le_mul hpow hlog hlogNonneg hpowYNonneg

lemma bipartiteNormalizedCount_clusters_rpow_log_le
    (H : FiniteFunctionFamily)
    (leftCenter rightCenter : C2Function) (radius : ℝ)
    (q centers support : ℕ)
    (hq : 0 < q)
    (hcenters : 0 < centers)
    (hsupport : 0 < support)
    (hupper : support < 2 * centers * (q + 1))
    (hnormalized :
      2 ≤ RectangleFamily.bipartiteNormalizedCount
        (H.cluster leftCenter radius)
        (H.cluster rightCenter radius) q q) :
    Real.rpow
          (RectangleFamily.bipartiteNormalizedCount
            (H.cluster leftCenter radius)
            (H.cluster rightCenter radius) q q)
          (3 / 2 : ℝ) *
        Real.log
          (RectangleFamily.bipartiteNormalizedCount
            (H.cluster leftCenter radius)
            (H.cluster rightCenter radius) q q) ≤
      Real.rpow
          (8 * (centers : ℝ) * (H.card : ℝ) /
            (support : ℝ))
          (3 / 2 : ℝ) *
        Real.log
          (8 * (centers : ℝ) * (H.card : ℝ) /
            (support : ℝ)) := by
  apply rpow_log_mono (by linarith)
  exact bipartiteNormalizedCount_clusters_le
    H leftCenter rightCenter radius q centers support
      hq hcenters hsupport hupper

lemma normal_count_scale_rpow
    (centers familyCard support : ℕ)
    (hcenters : 0 < centers)
    (hfamily : 0 < familyCard)
    (hsupport : 0 < support) :
    Real.rpow
        (8 * (centers : ℝ) * (familyCard : ℝ) /
          (support : ℝ))
        (3 / 2 : ℝ) =
      Real.rpow
          (8 * (centers : ℝ) * (familyCard : ℝ))
          (3 / 2 : ℝ) *
        Real.rpow (support : ℝ) (-3 / 2 : ℝ) := by
  have hnumerator :
      0 ≤ 8 * (centers : ℝ) * (familyCard : ℝ) := by
    positivity
  have hsupportNonneg : 0 ≤ (support : ℝ) := by
    positivity
  change
    (8 * (centers : ℝ) * (familyCard : ℝ) /
      (support : ℝ)) ^ (3 / 2 : ℝ) =
        (8 * (centers : ℝ) * (familyCard : ℝ)) ^
            (3 / 2 : ℝ) *
          (support : ℝ) ^ (-3 / 2 : ℝ)
  rw [Real.div_rpow hnumerator hsupportNonneg]
  have hsupportPos : 0 < (support : ℝ) := by
    exact_mod_cast hsupport
  rw [show (-3 / 2 : ℝ) = -(3 / 2 : ℝ) by ring,
    Real.rpow_neg hsupportPos.le, div_eq_mul_inv]

lemma normal_coarse_card_bound_with_support_decay
    (H : FiniteFunctionFamily)
    (leftCenter rightCenter : C2Function) (radius : ℝ)
    (q centers support : ℕ)
    (coarseCard : ℕ)
    (coefficient : ℝ)
    (hq : 0 < q)
    (hcenters : 0 < centers)
    (hsupport : 0 < support)
    (hupper : support < 2 * centers * (q + 1))
    (hnormalized :
      2 ≤ RectangleFamily.bipartiteNormalizedCount
        (H.cluster leftCenter radius)
        (H.cluster rightCenter radius) q q)
    (hcoarse :
      (coarseCard : ℝ) ≤
        (centers : ℝ) ^ 2 * coefficient *
          Real.rpow
            (RectangleFamily.bipartiteNormalizedCount
              (H.cluster leftCenter radius)
              (H.cluster rightCenter radius) q q)
            (3 / 2 : ℝ) *
          Real.log
            (RectangleFamily.bipartiteNormalizedCount
              (H.cluster leftCenter radius)
              (H.cluster rightCenter radius) q q))
    (hcoefficient : 0 ≤ coefficient) :
    (coarseCard : ℝ) ≤
      (centers : ℝ) ^ 2 * coefficient *
        Real.rpow
          (8 * (centers : ℝ) * (H.card : ℝ))
          (3 / 2 : ℝ) *
        Real.rpow (support : ℝ) (-3 / 2 : ℝ) *
        Real.log
          (8 * (centers : ℝ) * (H.card : ℝ) /
            (support : ℝ)) := by
  let normalized :=
    RectangleFamily.bipartiteNormalizedCount
      (H.cluster leftCenter radius)
      (H.cluster rightCenter radius) q q
  let upper :=
    8 * (centers : ℝ) * (H.card : ℝ) /
      (support : ℝ)
  have hmono :
      Real.rpow normalized (3 / 2 : ℝ) *
          Real.log normalized ≤
        Real.rpow upper (3 / 2 : ℝ) *
          Real.log upper := by
    exact bipartiteNormalizedCount_clusters_rpow_log_le
      H leftCenter rightCenter radius q centers support
        hq hcenters hsupport hupper hnormalized
  have hprefactor :
      0 ≤ (centers : ℝ) ^ 2 * coefficient := by
    positivity
  have hcoarse' :
      (coarseCard : ℝ) ≤
        ((centers : ℝ) ^ 2 * coefficient) *
          (Real.rpow normalized (3 / 2 : ℝ) *
            Real.log normalized) := by
    simpa [normalized, mul_assoc] using hcoarse
  have hupperBound :
      (coarseCard : ℝ) ≤
        ((centers : ℝ) ^ 2 * coefficient) *
          (Real.rpow upper (3 / 2 : ℝ) *
            Real.log upper) :=
    hcoarse'.trans
      (mul_le_mul_of_nonneg_left hmono hprefactor)
  have hHcard : 0 < H.card := by
    have hnormalizedUpper :
        normalized ≤ upper :=
      bipartiteNormalizedCount_clusters_le
        H leftCenter rightCenter radius q centers support
          hq hcenters hsupport hupper
    have hupperPos : 0 < upper := by
      have : 0 < normalized := by
        dsimp only [normalized]
        linarith
      exact this.trans_le hnormalizedUpper
    by_contra h
    have hzero : H.card = 0 := Nat.eq_zero_of_not_pos h
    dsimp only [upper] at hupperPos
    rw [hzero] at hupperPos
    norm_num at hupperPos
  have hscale :=
    normal_count_scale_rpow centers H.card support
      hcenters hHcard hsupport
  dsimp only [upper] at hupperBound ⊢
  rw [hscale] at hupperBound
  simpa [mul_assoc] using hupperBound

lemma support_rpow_cancel
    (support : ℕ) (hsupport : 0 < support) :
    Real.rpow (support : ℝ) (3 / 2 : ℝ) *
        Real.rpow (support : ℝ) (-3 / 2 : ℝ) = 1 := by
  have hsupportReal : 0 < (support : ℝ) := by
    exact_mod_cast hsupport
  calc
    Real.rpow (support : ℝ) (3 / 2 : ℝ) *
        Real.rpow (support : ℝ) (-3 / 2 : ℝ) =
      Real.rpow (support : ℝ)
        ((3 / 2 : ℝ) + (-3 / 2 : ℝ)) :=
      (Real.rpow_add hsupportReal _ _).symm
    _ = 1 := by norm_num

lemma representative_pair_incidence_tangency_bound
    (multiplicity q mu support : ℕ)
    (retention incidenceScale : ℝ)
    (hq : 2 ≤ q)
    (hmu : 0 < mu)
    (hretention : 0 < retention)
    (hscale : 0 ≤ incidenceScale)
    (hqRetention :
      retention * (mu : ℝ) < 4 * ((q : ℝ) + 1))
    (hincidence :
      (multiplicity : ℝ) * (q : ℝ) ^ 2 ≤
        3 * (support : ℝ) ^ 2 * incidenceScale) :
    (multiplicity : ℝ) ≤
      (108 * incidenceScale * Real.rpow retention (-2)) *
        Real.rpow (mu : ℝ) (-2) *
        Real.rpow (support : ℝ) 2 := by
  have hqReal : 2 ≤ (q : ℝ) := by
    exact_mod_cast hq
  have hmuReal : 0 < (mu : ℝ) := by
    exact_mod_cast hmu
  have hqPos : 0 < (q : ℝ) := by
    linarith
  have hqUpper :
      4 * ((q : ℝ) + 1) ≤ 6 * (q : ℝ) := by
    linarith
  have hretentionMu :
      retention * (mu : ℝ) ≤ 6 * (q : ℝ) :=
    (hqRetention.trans_le hqUpper).le
  have hsquareRaw :
      (retention * (mu : ℝ)) ^ 2 ≤
        (6 * (q : ℝ)) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).2 hretentionMu
  have hsquare :
      retention ^ 2 * (mu : ℝ) ^ 2 ≤
        36 * (q : ℝ) ^ 2 := by
    nlinarith [hsquareRaw]
  have hden :
      0 < retention ^ 2 * (mu : ℝ) ^ 2 := by
    positivity
  have hratio :
      1 ≤ 36 * (q : ℝ) ^ 2 /
        (retention ^ 2 * (mu : ℝ) ^ 2) := by
    apply (le_div_iff₀ hden).2
    simpa only [one_mul] using hsquare
  have hprefactor :
      0 ≤ 3 * (support : ℝ) ^ 2 * incidenceScale := by
    positivity
  have hscaled :
      3 * (support : ℝ) ^ 2 * incidenceScale ≤
        (3 * (support : ℝ) ^ 2 * incidenceScale) *
          (36 * (q : ℝ) ^ 2 /
            (retention ^ 2 * (mu : ℝ) ^ 2)) := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hratio hprefactor
  have hrpowRetention :
      Real.rpow retention (-2) = (retention ^ 2)⁻¹ := by
    calc
      Real.rpow retention (-2) =
          (Real.rpow retention (2 : ℝ))⁻¹ :=
        Real.rpow_neg hretention.le (2 : ℝ)
      _ = (retention ^ 2)⁻¹ :=
        congrArg Inv.inv (Real.rpow_two retention)
  have hrpowMu :
      Real.rpow (mu : ℝ) (-2) = ((mu : ℝ) ^ 2)⁻¹ := by
    calc
      Real.rpow (mu : ℝ) (-2) =
          (Real.rpow (mu : ℝ) (2 : ℝ))⁻¹ :=
        Real.rpow_neg hmuReal.le (2 : ℝ)
      _ = ((mu : ℝ) ^ 2)⁻¹ :=
        congrArg Inv.inv (Real.rpow_two (mu : ℝ))
  have hrpowSupport :
      Real.rpow (support : ℝ) 2 = (support : ℝ) ^ 2 :=
    Real.rpow_natCast (support : ℝ) 2
  have hscaled' :
      3 * (support : ℝ) ^ 2 * incidenceScale ≤
        ((108 * incidenceScale * Real.rpow retention (-2)) *
          Real.rpow (mu : ℝ) (-2) *
          Real.rpow (support : ℝ) 2) * (q : ℝ) ^ 2 := by
    rw [hrpowRetention, hrpowMu, hrpowSupport]
    rw [inv_eq_one_div, inv_eq_one_div]
    calc
      3 * (support : ℝ) ^ 2 * incidenceScale ≤
          (3 * (support : ℝ) ^ 2 * incidenceScale) *
            (36 * (q : ℝ) ^ 2 /
              (retention ^ 2 * (mu : ℝ) ^ 2)) :=
        hscaled
      _ =
          ((108 * incidenceScale * (1 / retention ^ 2)) *
            (1 / (mu : ℝ) ^ 2) * (support : ℝ) ^ 2) *
              (q : ℝ) ^ 2 := by
        field_simp <;> ring
  have hproduct :
      (multiplicity : ℝ) * (q : ℝ) ^ 2 ≤
        ((108 * incidenceScale * Real.rpow retention (-2)) *
          Real.rpow (mu : ℝ) (-2) *
          Real.rpow (support : ℝ) 2) * (q : ℝ) ^ 2 :=
    hincidence.trans hscaled'
  exact le_of_mul_le_mul_right hproduct (sq_pos_of_pos hqPos)

lemma selected_parent_tangency_bound
    (multiplicity q pairLower mu support parentEdges
      selectedRectangles : ℕ)
    (retention parentLoss rectangleLoss fiberBound
      incidenceScale : ℝ)
    (hq : 2 ≤ q)
    (hmu : 0 < mu)
    (hretention : 0 < retention)
    (hparentLoss : 0 ≤ parentLoss)
    (hrectangleLoss : 0 < rectangleLoss)
    (hfiberBound : 0 < fiberBound)
    (_hscale : 0 ≤ incidenceScale)
    (hqRetention :
      retention * (mu : ℝ) < 4 * ((q : ℝ) + 1))
    (hparentEdges :
      (multiplicity : ℝ) * (q : ℝ) ≤
        parentLoss * (parentEdges : ℝ))
    (hselected :
      (((parentEdges : ℝ) / 2) / fiberBound) ≤
        (selectedRectangles : ℝ))
    (hpairLower :
      (q : ℝ) ≤
        2 * rectangleLoss * (pairLower : ℝ))
    (hpairs :
      (selectedRectangles : ℝ) * (pairLower : ℝ) ^ 2 ≤
        3 * (support : ℝ) ^ 2 * incidenceScale) :
    (multiplicity : ℝ) ≤
      (5184 * incidenceScale * fiberBound * parentLoss *
          rectangleLoss ^ 2 * Real.rpow retention (-3)) *
        Real.rpow (mu : ℝ) (-3) *
        Real.rpow (support : ℝ) 2 := by
  have hqReal : 2 ≤ (q : ℝ) := by
    exact_mod_cast hq
  have hmuReal : 0 < (mu : ℝ) := by
    exact_mod_cast hmu
  have hparentEdgeUpper :
      (parentEdges : ℝ) ≤
        2 * fiberBound * (selectedRectangles : ℝ) := by
    have h := (div_le_iff₀ hfiberBound).mp hselected
    nlinarith
  have hmultiplicityEdge :
      (multiplicity : ℝ) * (q : ℝ) ≤
        2 * parentLoss * fiberBound *
          (selectedRectangles : ℝ) := by
    calc
      (multiplicity : ℝ) * (q : ℝ) ≤
          parentLoss * (parentEdges : ℝ) := hparentEdges
      _ ≤ parentLoss *
          (2 * fiberBound * (selectedRectangles : ℝ)) :=
        mul_le_mul_of_nonneg_left hparentEdgeUpper hparentLoss
      _ = 2 * parentLoss * fiberBound *
          (selectedRectangles : ℝ) := by ring
  have hqSquare :
      (q : ℝ) ^ 2 ≤
        4 * rectangleLoss ^ 2 * (pairLower : ℝ) ^ 2 := by
    have hsquare :=
      (sq_le_sq₀ (by positivity) (by positivity)).2 hpairLower
    nlinarith [hsquare]
  have hmulPair :
      (multiplicity : ℝ) * (q : ℝ) *
          (pairLower : ℝ) ^ 2 ≤
        6 * parentLoss * fiberBound *
          (support : ℝ) ^ 2 * incidenceScale := by
    calc
      (multiplicity : ℝ) * (q : ℝ) *
          (pairLower : ℝ) ^ 2 ≤
        (2 * parentLoss * fiberBound *
          (selectedRectangles : ℝ)) *
            (pairLower : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hmultiplicityEdge
          (sq_nonneg (pairLower : ℝ))
      _ ≤ (2 * parentLoss * fiberBound) *
          (3 * (support : ℝ) ^ 2 * incidenceScale) := by
        have hnonneg :
            0 ≤ 2 * parentLoss * fiberBound := by
          positivity
        calc
          (2 * parentLoss * fiberBound *
              (selectedRectangles : ℝ)) *
                (pairLower : ℝ) ^ 2 =
            (2 * parentLoss * fiberBound) *
              ((selectedRectangles : ℝ) *
                (pairLower : ℝ) ^ 2) := by ring
          _ ≤ (2 * parentLoss * fiberBound) *
              (3 * (support : ℝ) ^ 2 * incidenceScale) :=
            mul_le_mul_of_nonneg_left hpairs hnonneg
      _ = 6 * parentLoss * fiberBound *
          (support : ℝ) ^ 2 * incidenceScale := by ring
  have hmultiplicityNonneg :
      0 ≤ (multiplicity : ℝ) := by
    positivity
  have hMqCube :
      (multiplicity : ℝ) * (q : ℝ) ^ 3 ≤
        24 * parentLoss * fiberBound * rectangleLoss ^ 2 *
          (support : ℝ) ^ 2 * incidenceScale := by
    calc
      (multiplicity : ℝ) * (q : ℝ) ^ 3 =
          ((multiplicity : ℝ) * (q : ℝ)) *
            (q : ℝ) ^ 2 := by ring
      _ ≤ ((multiplicity : ℝ) * (q : ℝ)) *
          (4 * rectangleLoss ^ 2 * (pairLower : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hqSquare (by positivity)
      _ = 4 * rectangleLoss ^ 2 *
          ((multiplicity : ℝ) * (q : ℝ) *
            (pairLower : ℝ) ^ 2) := by ring
      _ ≤ 4 * rectangleLoss ^ 2 *
          (6 * parentLoss * fiberBound *
            (support : ℝ) ^ 2 * incidenceScale) :=
        mul_le_mul_of_nonneg_left hmulPair (by positivity)
      _ = 24 * parentLoss * fiberBound * rectangleLoss ^ 2 *
          (support : ℝ) ^ 2 * incidenceScale := by ring
  have hqUpper :
      4 * ((q : ℝ) + 1) ≤ 6 * (q : ℝ) := by
    linarith
  have hretentionMu :
      retention * (mu : ℝ) ≤ 6 * (q : ℝ) :=
    (hqRetention.trans_le hqUpper).le
  have hcubeRaw :
      (retention * (mu : ℝ)) ^ 3 ≤
        (6 * (q : ℝ)) ^ 3 :=
    pow_le_pow_left₀ (by positivity) hretentionMu 3
  have hcube :
      retention ^ 3 * (mu : ℝ) ^ 3 ≤
        216 * (q : ℝ) ^ 3 := by
    nlinarith [hcubeRaw]
  have hden :
      0 < retention ^ 3 * (mu : ℝ) ^ 3 := by
    positivity
  have hcombined :
      (multiplicity : ℝ) *
          (retention ^ 3 * (mu : ℝ) ^ 3) ≤
        5184 * incidenceScale * fiberBound * parentLoss *
          rectangleLoss ^ 2 * (support : ℝ) ^ 2 := by
    calc
      (multiplicity : ℝ) *
          (retention ^ 3 * (mu : ℝ) ^ 3) ≤
        (multiplicity : ℝ) * (216 * (q : ℝ) ^ 3) :=
          mul_le_mul_of_nonneg_left hcube hmultiplicityNonneg
      _ = 216 * ((multiplicity : ℝ) * (q : ℝ) ^ 3) := by
        ring
      _ ≤ 216 *
          (24 * parentLoss * fiberBound * rectangleLoss ^ 2 *
            (support : ℝ) ^ 2 * incidenceScale) := by
        gcongr
      _ = 5184 * incidenceScale * fiberBound * parentLoss *
          rectangleLoss ^ 2 * (support : ℝ) ^ 2 := by
        ring
  have hrpowRetention :
      Real.rpow retention (-3) = (retention ^ 3)⁻¹ := by
    calc
      Real.rpow retention (-3) =
          (Real.rpow retention (3 : ℝ))⁻¹ :=
        Real.rpow_neg hretention.le (3 : ℝ)
      _ = (retention ^ 3)⁻¹ :=
        congrArg Inv.inv (Real.rpow_natCast retention 3)
  have hrpowMu :
      Real.rpow (mu : ℝ) (-3) = ((mu : ℝ) ^ 3)⁻¹ := by
    calc
      Real.rpow (mu : ℝ) (-3) =
          (Real.rpow (mu : ℝ) (3 : ℝ))⁻¹ :=
        Real.rpow_neg hmuReal.le (3 : ℝ)
      _ = ((mu : ℝ) ^ 3)⁻¹ :=
        congrArg Inv.inv (Real.rpow_natCast (mu : ℝ) 3)
  have hrpowSupport :
      Real.rpow (support : ℝ) 2 = (support : ℝ) ^ 2 :=
    Real.rpow_natCast (support : ℝ) 2
  have htargetMul :
      (multiplicity : ℝ) *
          (retention ^ 3 * (mu : ℝ) ^ 3) ≤
        ((5184 * incidenceScale * fiberBound * parentLoss *
            rectangleLoss ^ 2 * Real.rpow retention (-3)) *
          Real.rpow (mu : ℝ) (-3) *
          Real.rpow (support : ℝ) 2) *
            (retention ^ 3 * (mu : ℝ) ^ 3) := by
    rw [hrpowRetention, hrpowMu, hrpowSupport]
    rw [inv_eq_one_div, inv_eq_one_div]
    calc
      (multiplicity : ℝ) *
          (retention ^ 3 * (mu : ℝ) ^ 3) ≤
        5184 * incidenceScale * fiberBound * parentLoss *
          rectangleLoss ^ 2 * (support : ℝ) ^ 2 :=
        hcombined
      _ =
        ((5184 * incidenceScale * fiberBound * parentLoss *
            rectangleLoss ^ 2 * (1 / retention ^ 3)) *
          (1 / (mu : ℝ) ^ 3) * (support : ℝ) ^ 2) *
            (retention ^ 3 * (mu : ℝ) ^ 3) := by
        field_simp
  exact le_of_mul_le_mul_right htargetMul hden

lemma selected_parent_tangency_bound_of_fiber_scale
    (multiplicity q pairLower mu support parentEdges
      selectedRectangles : ℕ)
    (retention parentLoss rectangleLoss fiberBound
      fiberCoefficient incidenceScale : ℝ)
    (hq : 2 ≤ q)
    (hmu : 0 < mu)
    (hretention : 0 < retention)
    (hparentLoss : 0 ≤ parentLoss)
    (hrectangleLoss : 0 < rectangleLoss)
    (hfiberBound : 0 < fiberBound)
    (hscale : 0 ≤ incidenceScale)
    (hfiberScale :
      fiberBound ≤ fiberCoefficient * (mu : ℝ))
    (hqRetention :
      retention * (mu : ℝ) < 4 * ((q : ℝ) + 1))
    (hparentEdges :
      (multiplicity : ℝ) * (q : ℝ) ≤
        parentLoss * (parentEdges : ℝ))
    (hselected :
      (((parentEdges : ℝ) / 2) / fiberBound) ≤
        (selectedRectangles : ℝ))
    (hpairLower :
      (q : ℝ) ≤
        2 * rectangleLoss * (pairLower : ℝ))
    (hpairs :
      (selectedRectangles : ℝ) * (pairLower : ℝ) ^ 2 ≤
        3 * (support : ℝ) ^ 2 * incidenceScale) :
    (multiplicity : ℝ) ≤
      (5184 * incidenceScale * fiberCoefficient * parentLoss *
          rectangleLoss ^ 2 * Real.rpow retention (-3)) *
        Real.rpow (mu : ℝ) (-2) *
        Real.rpow (support : ℝ) 2 := by
  have hraw :=
    selected_parent_tangency_bound
      multiplicity q pairLower mu support parentEdges
      selectedRectangles retention parentLoss rectangleLoss
      fiberBound incidenceScale hq hmu hretention hparentLoss
      hrectangleLoss hfiberBound hscale hqRetention hparentEdges
      hselected hpairLower hpairs
  have hmuReal : 0 < (mu : ℝ) := by
    exact_mod_cast hmu
  have hretentionPowNonneg :
      0 ≤ Real.rpow retention (-3) :=
    Real.rpow_nonneg hretention.le _
  have hbaseNonneg :
      0 ≤ 5184 * incidenceScale * parentLoss *
        rectangleLoss ^ 2 * Real.rpow retention (-3) := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by positivity) hscale)
          hparentLoss)
        (sq_nonneg rectangleLoss))
      hretentionPowNonneg
  have hsupportNonneg :
      0 ≤ Real.rpow (support : ℝ) 2 :=
    Real.rpow_nonneg (Nat.cast_nonneg support) _
  have hreplace :
      5184 * incidenceScale * fiberBound * parentLoss *
          rectangleLoss ^ 2 * Real.rpow retention (-3) ≤
        (5184 * incidenceScale * parentLoss *
          rectangleLoss ^ 2 * Real.rpow retention (-3)) *
            (fiberCoefficient * (mu : ℝ)) := by
    calc
      5184 * incidenceScale * fiberBound * parentLoss *
          rectangleLoss ^ 2 * Real.rpow retention (-3) =
        (5184 * incidenceScale * parentLoss *
          rectangleLoss ^ 2 * Real.rpow retention (-3)) *
            fiberBound := by ring
      _ ≤ (5184 * incidenceScale * parentLoss *
          rectangleLoss ^ 2 * Real.rpow retention (-3)) *
            (fiberCoefficient * (mu : ℝ)) :=
        mul_le_mul_of_nonneg_left hfiberScale hbaseNonneg
  have hmul :
      (5184 * incidenceScale * fiberBound * parentLoss *
          rectangleLoss ^ 2 * Real.rpow retention (-3)) *
          Real.rpow (mu : ℝ) (-3) ≤
        ((5184 * incidenceScale * parentLoss *
          rectangleLoss ^ 2 * Real.rpow retention (-3)) *
            (fiberCoefficient * (mu : ℝ))) *
          Real.rpow (mu : ℝ) (-3) :=
    mul_le_mul_of_nonneg_right hreplace
      (Real.rpow_nonneg hmuReal.le _)
  have hmuCancel :
      (mu : ℝ) * Real.rpow (mu : ℝ) (-3) =
        Real.rpow (mu : ℝ) (-2) := by
    calc
      (mu : ℝ) * Real.rpow (mu : ℝ) (-3) =
          Real.rpow (mu : ℝ) 1 *
            Real.rpow (mu : ℝ) (-3) := by simp
      _ = Real.rpow (mu : ℝ) (1 + (-3)) :=
        (Real.rpow_add hmuReal 1 (-3)).symm
      _ = Real.rpow (mu : ℝ) (-2) := by norm_num
  calc
    (multiplicity : ℝ) ≤
      (5184 * incidenceScale * fiberBound * parentLoss *
          rectangleLoss ^ 2 * Real.rpow retention (-3)) *
        Real.rpow (mu : ℝ) (-3) *
        Real.rpow (support : ℝ) 2 :=
      hraw
    _ ≤
      (((5184 * incidenceScale * parentLoss *
          rectangleLoss ^ 2 * Real.rpow retention (-3)) *
            (fiberCoefficient * (mu : ℝ))) *
          Real.rpow (mu : ℝ) (-3)) *
        Real.rpow (support : ℝ) 2 :=
      mul_le_mul_of_nonneg_right hmul hsupportNonneg
    _ =
      (5184 * incidenceScale * fiberCoefficient * parentLoss *
          rectangleLoss ^ 2 * Real.rpow retention (-3)) *
        Real.rpow (mu : ℝ) (-2) *
        Real.rpow (support : ℝ) 2 := by
      rw [show
        ((5184 * incidenceScale * parentLoss *
            rectangleLoss ^ 2 * Real.rpow retention (-3)) *
              (fiberCoefficient * (mu : ℝ))) *
            Real.rpow (mu : ℝ) (-3) =
          (5184 * incidenceScale * fiberCoefficient * parentLoss *
            rectangleLoss ^ 2 * Real.rpow retention (-3)) *
              ((mu : ℝ) * Real.rpow (mu : ℝ) (-3)) by ring,
        hmuCancel]

lemma normal_selected_cardinality_transport
    (original retained rawEdges selectedEdges heavy
      selectedCoarse M q mu : ℕ)
    (parentLoss degreeLoss supportLoss fiberBound
      retention : ℝ)
    (hM : 0 < M)
    (hq : 2 ≤ q)
    (hmu : 0 < mu)
    (hparentLoss : 0 ≤ parentLoss)
    (hdegreeLoss : 0 ≤ degreeLoss)
    (hsupportLoss : 0 ≤ supportLoss)
    (hfiberBound : 0 < fiberBound)
    (hretention : 0 < retention)
    (horiginal :
      (original : ℝ) ≤ parentLoss * (retained : ℝ))
    (hrawLower :
      (retained : ℝ) * (q : ℝ) ≤ (rawEdges : ℝ))
    (hedgeRetention :
      (rawEdges : ℝ) ≤ degreeLoss * (selectedEdges : ℝ))
    (hheavyLower :
      ((selectedEdges : ℝ) / 2) /
          ((2 * (M : ℝ)) * fiberBound) ≤ (heavy : ℝ))
    (hsupportRetention :
      (heavy : ℝ) ≤ supportLoss * (selectedCoarse : ℝ))
    (hfiberScale : fiberBound ≤ 2 * (mu : ℝ))
    (hqRetention :
      retention * (mu : ℝ) < 4 * ((q : ℝ) + 1)) :
    (original : ℝ) ≤
      (48 * parentLoss * degreeLoss * supportLoss *
          Real.rpow retention (-1)) *
        (((M * selectedCoarse : ℕ) : ℝ)) := by
  have hMReal : 0 < (M : ℝ) := by
    exact_mod_cast hM
  have hqReal : 2 ≤ (q : ℝ) := by
    exact_mod_cast hq
  have hqPos : 0 < (q : ℝ) := by
    linarith
  have hmuReal : 0 < (mu : ℝ) := by
    exact_mod_cast hmu
  have hupper :
      0 < (2 * (M : ℝ)) * fiberBound := by
    positivity
  have hselectedUpper :
      (selectedEdges : ℝ) ≤
        4 * (M : ℝ) * fiberBound * (heavy : ℝ) := by
    have h := (div_le_iff₀ hupper).mp hheavyLower
    nlinarith
  have horiginalQ :
      (original : ℝ) * (q : ℝ) ≤
        4 * parentLoss * degreeLoss * (M : ℝ) *
          fiberBound * (heavy : ℝ) := by
    calc
      (original : ℝ) * (q : ℝ) ≤
          (parentLoss * (retained : ℝ)) * (q : ℝ) :=
        mul_le_mul_of_nonneg_right horiginal hqPos.le
      _ = parentLoss * ((retained : ℝ) * (q : ℝ)) := by
        ring
      _ ≤ parentLoss * (rawEdges : ℝ) :=
        mul_le_mul_of_nonneg_left hrawLower hparentLoss
      _ ≤ parentLoss * (degreeLoss * (selectedEdges : ℝ)) :=
        mul_le_mul_of_nonneg_left hedgeRetention hparentLoss
      _ ≤ parentLoss *
          (degreeLoss *
            (4 * (M : ℝ) * fiberBound * (heavy : ℝ))) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hselectedUpper hdegreeLoss)
          hparentLoss
      _ = 4 * parentLoss * degreeLoss * (M : ℝ) *
          fiberBound * (heavy : ℝ) := by
        ring
  have horiginalQSelected :
      (original : ℝ) * (q : ℝ) ≤
        4 * parentLoss * degreeLoss * supportLoss *
          (M : ℝ) * fiberBound * (selectedCoarse : ℝ) := by
    calc
      (original : ℝ) * (q : ℝ) ≤
          4 * parentLoss * degreeLoss * (M : ℝ) *
            fiberBound * (heavy : ℝ) :=
        horiginalQ
      _ ≤ 4 * parentLoss * degreeLoss * (M : ℝ) *
          fiberBound * (supportLoss * (selectedCoarse : ℝ)) := by
        exact mul_le_mul_of_nonneg_left
          hsupportRetention (by positivity)
      _ = 4 * parentLoss * degreeLoss * supportLoss *
          (M : ℝ) * fiberBound * (selectedCoarse : ℝ) := by
        ring
  have hqUpper :
      4 * ((q : ℝ) + 1) ≤ 6 * (q : ℝ) := by
    linarith
  have hretentionMu :
      retention * (mu : ℝ) ≤ 6 * (q : ℝ) :=
    (hqRetention.trans_le hqUpper).le
  have hretentionFiber :
      retention * fiberBound ≤ 12 * (q : ℝ) := by
    calc
      retention * fiberBound ≤
          retention * (2 * (mu : ℝ)) :=
        mul_le_mul_of_nonneg_left hfiberScale hretention.le
      _ = 2 * (retention * (mu : ℝ)) := by
        ring
      _ ≤ 2 * (6 * (q : ℝ)) := by
        gcongr
      _ = 12 * (q : ℝ) := by
        ring
  have hscaled :
      ((original : ℝ) * retention) * (q : ℝ) ≤
        (48 * parentLoss * degreeLoss * supportLoss *
          ((M * selectedCoarse : ℕ) : ℝ)) * (q : ℝ) := by
    calc
      ((original : ℝ) * retention) * (q : ℝ) =
          retention * ((original : ℝ) * (q : ℝ)) := by
        ring
      _ ≤ retention *
          (4 * parentLoss * degreeLoss * supportLoss *
            (M : ℝ) * fiberBound * (selectedCoarse : ℝ)) :=
        mul_le_mul_of_nonneg_left
          horiginalQSelected hretention.le
      _ = (4 * parentLoss * degreeLoss * supportLoss *
          (M : ℝ) * (selectedCoarse : ℝ)) *
            (retention * fiberBound) := by
        ring
      _ ≤ (4 * parentLoss * degreeLoss * supportLoss *
          (M : ℝ) * (selectedCoarse : ℝ)) *
            (12 * (q : ℝ)) :=
        mul_le_mul_of_nonneg_left hretentionFiber
          (by positivity)
      _ = (48 * parentLoss * degreeLoss * supportLoss *
          ((M * selectedCoarse : ℕ) : ℝ)) * (q : ℝ) := by
        norm_num [Nat.cast_mul]
        ring
  have hretainedCancel :
      (original : ℝ) * retention ≤
        48 * parentLoss * degreeLoss * supportLoss *
          ((M * selectedCoarse : ℕ) : ℝ) :=
    le_of_mul_le_mul_right hscaled hqPos
  have hrpowRetention :
      Real.rpow retention (-1) = retention⁻¹ := by
    calc
      Real.rpow retention (-1) =
          (Real.rpow retention (1 : ℝ))⁻¹ :=
        Real.rpow_neg hretention.le (1 : ℝ)
      _ = retention⁻¹ := by simp
  rw [hrpowRetention]
  rw [show
    48 * parentLoss * degreeLoss * supportLoss * retention⁻¹ *
        ((M * selectedCoarse : ℕ) : ℝ) =
      (48 * parentLoss * degreeLoss * supportLoss *
        ((M * selectedCoarse : ℕ) : ℝ)) * retention⁻¹ by ring]
  exact (le_mul_inv_iff₀ hretention).2 hretainedCancel

lemma coarse_interpolation_factorized
    (hInterpolate : CoarseMultiplicityInterpolationStatement)
    (multiplicity measureScale tangencyScale mu support : ℝ)
    (hmultiplicity : 0 ≤ multiplicity)
    (hmeasureScale : 0 ≤ measureScale)
    (htangencyScale : 0 ≤ tangencyScale)
    (hmu : 0 < mu)
    (hsupport : 0 < support)
    (hmeasure :
      multiplicity ≤ measureScale)
    (htangency :
      multiplicity ≤
        tangencyScale * Real.rpow mu (-2) *
          Real.rpow support 2) :
    multiplicity ≤
      (Real.rpow measureScale (1 / 4 : ℝ) *
        Real.rpow tangencyScale (3 / 4 : ℝ)) *
        Real.rpow mu (-3 / 2 : ℝ) *
        Real.rpow support (3 / 2 : ℝ) := by
  have htangencyBound :
      0 ≤
        tangencyScale * Real.rpow mu (-2) *
          Real.rpow support 2 := by
    exact mul_nonneg
      (mul_nonneg htangencyScale
        (Real.rpow_nonneg hmu.le (-2)))
      (Real.rpow_nonneg hsupport.le 2)
  have hmain :=
    hInterpolate multiplicity
      measureScale
      (tangencyScale * Real.rpow mu (-2) *
        Real.rpow support 2)
      hmultiplicity hmeasureScale htangencyBound
      hmeasure htangency
  have htangencyFactor :
      Real.rpow
          (tangencyScale * Real.rpow mu (-2) *
            Real.rpow support 2)
          (3 / 4 : ℝ) =
        Real.rpow tangencyScale (3 / 4 : ℝ) *
          Real.rpow mu (-3 / 2 : ℝ) *
          Real.rpow support (3 / 2 : ℝ) := by
    calc
      Real.rpow
          (tangencyScale * Real.rpow mu (-2) *
            Real.rpow support 2)
          (3 / 4 : ℝ) =
        Real.rpow
            (tangencyScale * Real.rpow mu (-2))
            (3 / 4 : ℝ) *
          Real.rpow (Real.rpow support 2)
            (3 / 4 : ℝ) := by
        exact Real.mul_rpow
          (mul_nonneg htangencyScale
            (Real.rpow_nonneg hmu.le (-2)))
          (Real.rpow_nonneg hsupport.le 2)
      _ =
        (Real.rpow tangencyScale (3 / 4 : ℝ) *
          Real.rpow (Real.rpow mu (-2)) (3 / 4 : ℝ)) *
          Real.rpow (Real.rpow support 2) (3 / 4 : ℝ) := by
        exact congrArg
          (fun value =>
            value * Real.rpow (Real.rpow support 2)
              (3 / 4 : ℝ))
          (Real.mul_rpow htangencyScale
            (Real.rpow_nonneg hmu.le (-2)))
      _ =
        Real.rpow tangencyScale (3 / 4 : ℝ) *
          Real.rpow mu (-3 / 2 : ℝ) *
          Real.rpow support (3 / 2 : ℝ) := by
        have hmuFlat :
            Real.rpow (Real.rpow mu (-2)) (3 / 4 : ℝ) =
              Real.rpow mu (-3 / 2 : ℝ) := by
          calc
            Real.rpow (Real.rpow mu (-2)) (3 / 4 : ℝ) =
                Real.rpow mu ((-2) * (3 / 4 : ℝ)) :=
              (Real.rpow_mul hmu.le _ _).symm
            _ = Real.rpow mu (-3 / 2 : ℝ) := by
              congr 1
              ring
        have hsupportFlat :
            Real.rpow (Real.rpow support 2) (3 / 4 : ℝ) =
              Real.rpow support (3 / 2 : ℝ) := by
          calc
            Real.rpow (Real.rpow support 2) (3 / 4 : ℝ) =
                Real.rpow support (2 * (3 / 4 : ℝ)) :=
              (Real.rpow_mul hsupport.le _ _).symm
            _ = Real.rpow support (3 / 2 : ℝ) := by
              congr 1
              ring
        rw [hmuFlat, hsupportFlat]
  rw [htangencyFactor] at hmain
  calc
    multiplicity ≤
        Real.rpow measureScale (1 / 4 : ℝ) *
        (Real.rpow tangencyScale (3 / 4 : ℝ) *
          Real.rpow mu (-3 / 2 : ℝ) *
          Real.rpow support (3 / 2 : ℝ)) :=
      hmain
    _ =
      (Real.rpow measureScale (1 / 4 : ℝ) *
        Real.rpow tangencyScale (3 / 4 : ℝ)) *
        Real.rpow mu (-3 / 2 : ℝ) *
        Real.rpow support (3 / 2 : ℝ) := by ring

lemma coarse_multiplicity_support_decay_cancel
    (finePerParent coarseCard mu support : ℕ)
    (scale coefficient tail : ℝ)
    (hmu : 0 < mu)
    (hsupport : 0 < support)
    (hscale : 0 ≤ scale)
    (hcoefficient : 0 ≤ coefficient)
    (htail : 0 ≤ tail)
    (hfine :
      (finePerParent : ℝ) ≤
        scale * Real.rpow (mu : ℝ) (-3 / 2 : ℝ) *
          Real.rpow (support : ℝ) (3 / 2 : ℝ))
    (hcoarse :
      (coarseCard : ℝ) ≤
        coefficient * Real.rpow (support : ℝ) (-3 / 2 : ℝ) *
          tail) :
    ((finePerParent * coarseCard : ℕ) : ℝ) ≤
      scale * coefficient * tail *
        Real.rpow (mu : ℝ) (-3 / 2 : ℝ) := by
  have hmuNonneg :
      0 ≤ Real.rpow (mu : ℝ) (-3 / 2 : ℝ) := by
    exact Real.rpow_nonneg (Nat.cast_nonneg mu) _
  have hsupportPos : 0 < (support : ℝ) := by
    exact_mod_cast hsupport
  have hsupportPosPow :
      0 ≤ Real.rpow (support : ℝ) (3 / 2 : ℝ) :=
    Real.rpow_nonneg hsupportPos.le _
  have hsupportNegPow :
      0 ≤ Real.rpow (support : ℝ) (-3 / 2 : ℝ) :=
    Real.rpow_nonneg hsupportPos.le _
  have hfineRhs :
      0 ≤
        scale * Real.rpow (mu : ℝ) (-3 / 2 : ℝ) *
          Real.rpow (support : ℝ) (3 / 2 : ℝ) := by
    positivity
  have hcoarseRhs :
      0 ≤
        coefficient * Real.rpow (support : ℝ) (-3 / 2 : ℝ) *
          tail := by
    positivity
  have hproduct :
      (finePerParent : ℝ) * (coarseCard : ℝ) ≤
        (scale * Real.rpow (mu : ℝ) (-3 / 2 : ℝ) *
            Real.rpow (support : ℝ) (3 / 2 : ℝ)) *
          (coefficient *
            Real.rpow (support : ℝ) (-3 / 2 : ℝ) * tail) :=
    mul_le_mul hfine hcoarse (Nat.cast_nonneg coarseCard) hfineRhs
  have hreorder :
      (scale * Real.rpow (mu : ℝ) (-3 / 2 : ℝ) *
          Real.rpow (support : ℝ) (3 / 2 : ℝ)) *
        (coefficient *
          Real.rpow (support : ℝ) (-3 / 2 : ℝ) * tail) =
      scale * coefficient * tail *
        Real.rpow (mu : ℝ) (-3 / 2 : ℝ) *
          (Real.rpow (support : ℝ) (3 / 2 : ℝ) *
            Real.rpow (support : ℝ) (-3 / 2 : ℝ)) := by
    ring
  rw [hreorder, support_rpow_cancel support hsupport, mul_one] at hproduct
  simpa [Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm] using hproduct

lemma normal_fine_card_bound_from_interpolation
    (hInterpolate : CoarseMultiplicityInterpolationStatement)
    (finePerParent coarseCard mu support : ℕ)
    (measureScale tangencyScale coefficient tail : ℝ)
    (hfinePerParent : 0 < finePerParent)
    (hmu : 0 < mu)
    (hsupport : 0 < support)
    (hmeasureScale : 0 ≤ measureScale)
    (htangencyScale : 0 ≤ tangencyScale)
    (hcoefficient : 0 ≤ coefficient)
    (htail : 0 ≤ tail)
    (hmeasure :
      (finePerParent : ℝ) ≤ measureScale)
    (htangency :
      (finePerParent : ℝ) ≤
        tangencyScale * Real.rpow (mu : ℝ) (-2) *
          Real.rpow (support : ℝ) 2)
    (hcoarse :
      (coarseCard : ℝ) ≤
        coefficient * Real.rpow (support : ℝ) (-3 / 2 : ℝ) *
          tail) :
    ((finePerParent * coarseCard : ℕ) : ℝ) ≤
      (Real.rpow measureScale (1 / 4 : ℝ) *
        Real.rpow tangencyScale (3 / 4 : ℝ)) *
        coefficient * tail *
        Real.rpow (mu : ℝ) (-3 / 2 : ℝ) := by
  have hfine :
      (finePerParent : ℝ) ≤
        (Real.rpow measureScale (1 / 4 : ℝ) *
          Real.rpow tangencyScale (3 / 4 : ℝ)) *
          Real.rpow (mu : ℝ) (-3 / 2 : ℝ) *
          Real.rpow (support : ℝ) (3 / 2 : ℝ) := by
    exact coarse_interpolation_factorized
      hInterpolate (finePerParent : ℝ)
      measureScale tangencyScale (mu : ℝ) (support : ℝ)
      (by exact_mod_cast hfinePerParent.le)
      hmeasureScale htangencyScale
      (by exact_mod_cast hmu)
      (by exact_mod_cast hsupport)
      hmeasure htangency
  have hscale :
      0 ≤ Real.rpow measureScale (1 / 4 : ℝ) *
        Real.rpow tangencyScale (3 / 4 : ℝ) := by
    exact mul_nonneg
      (Real.rpow_nonneg hmeasureScale _)
      (Real.rpow_nonneg htangencyScale _)
  exact coarse_multiplicity_support_decay_cancel
    finePerParent coarseCard mu support
    (Real.rpow measureScale (1 / 4 : ℝ) *
      Real.rpow tangencyScale (3 / 4 : ℝ))
    coefficient tail hmu hsupport hscale hcoefficient htail
    hfine hcoarse

lemma small_support_normal_fine_card_bound
    (finePerParent coarseCard mu support centers : ℕ)
    (scale coefficient tail : ℝ)
    (hmu : 0 < mu)
    (hsupport : 0 < support)
    (hsmall : support < 2 * centers)
    (hscale : 0 ≤ scale)
    (_hcoefficient : 0 ≤ coefficient)
    (_htail : 0 ≤ tail)
    (hfine :
      (finePerParent : ℝ) ≤
        scale * Real.rpow (mu : ℝ) (-3 / 2 : ℝ) *
          Real.rpow (support : ℝ) (3 / 2 : ℝ))
    (hcoarse :
      (coarseCard : ℝ) ≤ coefficient * tail) :
    (((finePerParent * coarseCard : ℕ) : ℝ)) ≤
      scale * coefficient * tail *
        Real.rpow (2 * (centers : ℝ)) (3 / 2 : ℝ) *
        Real.rpow (mu : ℝ) (-3 / 2 : ℝ) := by
  have hmuNonneg :
      0 ≤ Real.rpow (mu : ℝ) (-3 / 2 : ℝ) :=
    Real.rpow_nonneg (by positivity) _
  have hsupportPower :
      Real.rpow (support : ℝ) (3 / 2 : ℝ) ≤
        Real.rpow (2 * (centers : ℝ)) (3 / 2 : ℝ) := by
    apply Real.rpow_le_rpow
    · positivity
    · exact_mod_cast hsmall.le
    · norm_num
  have hfine' :
      (finePerParent : ℝ) ≤
        scale * Real.rpow (mu : ℝ) (-3 / 2 : ℝ) *
          Real.rpow (2 * (centers : ℝ)) (3 / 2 : ℝ) :=
    hfine.trans
      (mul_le_mul_of_nonneg_left hsupportPower (by positivity))
  have hfineRhsNonneg :
      0 ≤ scale * Real.rpow (mu : ℝ) (-3 / 2 : ℝ) *
        Real.rpow (2 * (centers : ℝ)) (3 / 2 : ℝ) := by
    exact mul_nonneg
      (mul_nonneg hscale hmuNonneg)
      (Real.rpow_nonneg (by positivity) _)
  have hproduct :=
    mul_le_mul hfine' hcoarse
      (Nat.cast_nonneg coarseCard) hfineRhsNonneg
  calc
    (((finePerParent * coarseCard : ℕ) : ℝ)) =
        (finePerParent : ℝ) * (coarseCard : ℝ) := by
      norm_num
    _ ≤
      (scale * Real.rpow (mu : ℝ) (-3 / 2 : ℝ) *
          Real.rpow (2 * (centers : ℝ)) (3 / 2 : ℝ)) *
        (coefficient * tail) :=
      hproduct
    _ = scale * coefficient * tail *
        Real.rpow (2 * (centers : ℝ)) (3 / 2 : ℝ) *
        Real.rpow (mu : ℝ) (-3 / 2 : ℝ) := by
      ring

end Kakeya.Cinematic

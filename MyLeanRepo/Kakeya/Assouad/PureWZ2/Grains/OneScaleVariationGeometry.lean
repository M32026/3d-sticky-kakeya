import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.DirectionAlignment
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.DirectionOverlap
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.RobustCloseCountPhase1
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.TransversePairPaper

/-!
# One-scale plane-map variation: geometric core

This module isolates the part of the paper's Lemma 14 which follows from the
literal Section 6 cover relation.  It deliberately contains no mass-selection
or reverse-association premise.

* A transverse fine pair covered by two coarse parents remains transverse,
  with the explicit loss of two cover-direction errors.
* If two unit plane-map values are nearly orthogonal to the same transverse
  coarse parent pair and have the same cross-product orientation, their
  variation is controlled by `direction_overlap_lemma`.
* The paper-normalized `2 * rho` conclusion is obtained from the exact
  arithmetic condition `6 * incidence / coarseKappa <= 2 * rho`.

The remaining combinatorial step is to refine the shading so that one common
parent pair and one orientation are retained in each relevant coarse cell.
-/

noncomputable section

namespace Kakeya.Assouad

open InnerProductGeometry

attribute [local instance] Classical.propDecidable

/-- Elementary norm bound for the three-dimensional cross product. -/
private lemma oneScale_wz1Cross_norm_le (a b : Point3) :
    ‖wz1Cross a b‖ ≤ ‖a‖ * ‖b‖ := by
  have h :
      ‖wz1Cross a b‖ =
        ‖a‖ * ‖b‖ * Real.sin (InnerProductGeometry.angle a b) :=
    InnerProductGeometry.norm_ofLp_crossProduct a b
  rw [h]
  have hsin : Real.sin (InnerProductGeometry.angle a b) ≤ 1 :=
    Real.sin_le_one _
  have hnonneg : 0 ≤ ‖a‖ * ‖b‖ := by positivity
  nlinarith

/-- Bilinear Lipschitz bound for the cross product. -/
private lemma wz1Cross_lipschitz (a a' b b' : Point3) :
    ‖wz1Cross a b - wz1Cross a' b'‖ ≤
      ‖a - a'‖ * ‖b‖ + ‖a'‖ * ‖b - b'‖ := by
  have h_add1 :
      wz1Cross a b = wz1Cross a' b + wz1Cross (a - a') b := by
    unfold wz1Cross
    have h_eq :
        (a : Fin 3 → ℝ) =
          (a' : Fin 3 → ℝ) + ((a - a') : Fin 3 → ℝ) := by
      ext i
      simp [sub_add_cancel]
    rw [h_eq]
    have h2 :
        crossProduct
            ((a' : Fin 3 → ℝ) + ((a - a') : Fin 3 → ℝ))
            (b : Fin 3 → ℝ) =
          crossProduct (a' : Fin 3 → ℝ) (b : Fin 3 → ℝ) +
            crossProduct ((a - a') : Fin 3 → ℝ) (b : Fin 3 → ℝ) := by
      have h3 :=
        crossProduct.map_add
          (a' : Fin 3 → ℝ) ((a - a') : Fin 3 → ℝ)
      simpa [h3] using rfl
    rw [h2] <;> rfl
  have h_add2 :
      wz1Cross a' b = wz1Cross a' b' + wz1Cross a' (b - b') := by
    unfold wz1Cross
    have h_eq :
        (b : Fin 3 → ℝ) =
          (b' : Fin 3 → ℝ) + ((b - b') : Fin 3 → ℝ) := by
      ext i
      simp [sub_add_cancel]
    rw [h_eq]
    have h2 :
        crossProduct (a' : Fin 3 → ℝ)
            ((b' : Fin 3 → ℝ) + ((b - b') : Fin 3 → ℝ)) =
          crossProduct (a' : Fin 3 → ℝ) (b' : Fin 3 → ℝ) +
            crossProduct (a' : Fin 3 → ℝ) ((b - b') : Fin 3 → ℝ) := by
      have h3 :=
        (crossProduct (a' : Fin 3 → ℝ)).map_add
          (b' : Fin 3 → ℝ) ((b - b') : Fin 3 → ℝ)
      simpa [h3] using rfl
    rw [h2] <;> rfl
  have h_main :
      wz1Cross a b - wz1Cross a' b' =
        wz1Cross (a - a') b + wz1Cross a' (b - b') := by
    rw [h_add1, h_add2] <;> abel
  rw [h_main]
  calc
    ‖wz1Cross (a - a') b + wz1Cross a' (b - b')‖
        ≤ ‖wz1Cross (a - a') b‖ + ‖wz1Cross a' (b - b')‖ :=
          norm_add_le _ _
    _ ≤ ‖a - a'‖ * ‖b‖ + ‖a'‖ * ‖b - b'‖ := by
      exact add_le_add (oneScale_wz1Cross_norm_le (a - a') b)
        (oneScale_wz1Cross_norm_le a' (b - b'))

/-- The cross product is Lipschitz in both unit-vector arguments. -/
lemma wz1Cross_sub_norm_le_of_unit
    {u v u' v' : Point3} {epsilon : ℝ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hu' : ‖u'‖ = 1) (hv' : ‖v'‖ = 1)
    (huu' : ‖u - u'‖ ≤ epsilon)
    (hvv' : ‖v - v'‖ ≤ epsilon) :
    ‖wz1Cross u v - wz1Cross u' v'‖ ≤ 2 * epsilon := by
  calc
    ‖wz1Cross u v - wz1Cross u' v'‖
        ≤ ‖u - u'‖ * ‖v‖ + ‖u'‖ * ‖v - v'‖ :=
          wz1Cross_lipschitz u u' v v'
    _ = ‖u - u'‖ + ‖v - v'‖ := by rw [hv, hu'] <;> ring
    _ ≤ epsilon + epsilon := by gcongr
    _ = 2 * epsilon := by ring

/-- Transversality survives passage from fine tubes to their coarse parents.

Each cover changes a paper direction by at most `rho / 2`, so the cross
product norm loses at most `rho` in total. -/
lemma paper_cover_parent_pair_transverse
    {delta rho kappa : ℝ}
    {fineFirst fineSecond : Kakeya.DeltaTube delta}
    {coarseFirst coarseSecond : Kakeya.DeltaTube rho}
    (hfirst : WZ1PaperTubeCovers fineFirst coarseFirst)
    (hsecond : WZ1PaperTubeCovers fineSecond coarseSecond)
    (htransverse :
      kappa ≤
        ‖wz1Cross (wz1PaperDirection fineFirst)
          (wz1PaperDirection fineSecond)‖) :
    kappa - rho ≤
      ‖wz1Cross (wz1PaperDirection coarseFirst)
        (wz1PaperDirection coarseSecond)‖ := by
  have hfirstUnit : ‖wz1PaperDirection fineFirst‖ = 1 :=
    wz1PaperDirection_norm fineFirst
  have hsecondUnit : ‖wz1PaperDirection fineSecond‖ = 1 :=
    wz1PaperDirection_norm fineSecond
  have hcoarseFirstUnit : ‖wz1PaperDirection coarseFirst‖ = 1 :=
    wz1PaperDirection_norm coarseFirst
  have hcoarseSecondUnit : ‖wz1PaperDirection coarseSecond‖ = 1 :=
    wz1PaperDirection_norm coarseSecond
  have hfirstAlign :
      ‖wz1PaperDirection fineFirst - wz1PaperDirection coarseFirst‖ ≤ rho / 2 :=
    paper_cover_direction_alignment hfirst
  have hsecondAlign :
      ‖wz1PaperDirection fineSecond - wz1PaperDirection coarseSecond‖ ≤ rho / 2 :=
    paper_cover_direction_alignment hsecond
  have hcrossDiff :
      ‖wz1Cross (wz1PaperDirection fineFirst)
          (wz1PaperDirection fineSecond) -
        wz1Cross (wz1PaperDirection coarseFirst)
          (wz1PaperDirection coarseSecond)‖ ≤ rho := by
    have h := wz1Cross_sub_norm_le_of_unit
      hfirstUnit hsecondUnit hcoarseFirstUnit hcoarseSecondUnit
      hfirstAlign hsecondAlign
    linarith
  have hnormReverse :
      ‖wz1Cross (wz1PaperDirection fineFirst)
          (wz1PaperDirection fineSecond)‖ ≤
        ‖wz1Cross (wz1PaperDirection coarseFirst)
          (wz1PaperDirection coarseSecond)‖ + rho := by
    calc
      ‖wz1Cross (wz1PaperDirection fineFirst)
          (wz1PaperDirection fineSecond)‖
          ≤ ‖wz1Cross (wz1PaperDirection fineFirst)
                (wz1PaperDirection fineSecond) -
              wz1Cross (wz1PaperDirection coarseFirst)
                (wz1PaperDirection coarseSecond)‖ +
              ‖wz1Cross (wz1PaperDirection coarseFirst)
                (wz1PaperDirection coarseSecond)‖ := by
            exact norm_le_norm_sub_add _ _
      _ ≤ rho +
              ‖wz1Cross (wz1PaperDirection coarseFirst)
                (wz1PaperDirection coarseSecond)‖ := by gcongr
      _ = ‖wz1Cross (wz1PaperDirection coarseFirst)
              (wz1PaperDirection coarseSecond)‖ + rho := by ring
  linarith

/-- A fine plane-map incidence bound transfers to a covered coarse parent. -/
lemma paper_cover_parent_incidence
    {delta rho incidence : ℝ}
    {fine : Kakeya.DeltaTube delta}
    {coarse : Kakeya.DeltaTube rho}
    {normal : Point3}
    (hcover : WZ1PaperTubeCovers fine coarse)
    (hnormal : ‖normal‖ = 1)
    (hfine :
      |inner ℝ (wz1PaperDirection fine) normal| ≤ incidence) :
    |inner ℝ (wz1PaperDirection coarse) normal| ≤ incidence + rho / 2 := by
  have halign :
      ‖wz1PaperDirection coarse - wz1PaperDirection fine‖ ≤ rho / 2 := by
    rw [norm_sub_rev]
    exact paper_cover_direction_alignment hcover
  have hdiff :
      |inner ℝ
          (wz1PaperDirection coarse - wz1PaperDirection fine) normal| ≤
        rho / 2 := by
    calc
      |inner ℝ
          (wz1PaperDirection coarse - wz1PaperDirection fine) normal|
          ≤ ‖wz1PaperDirection coarse - wz1PaperDirection fine‖ * ‖normal‖ :=
            abs_real_inner_le_norm _ _
      _ = ‖wz1PaperDirection coarse - wz1PaperDirection fine‖ := by
            rw [hnormal] <;> ring
      _ ≤ rho / 2 := halign
  have hdecomp :
      inner ℝ (wz1PaperDirection coarse) normal =
        inner ℝ (wz1PaperDirection fine) normal +
          inner ℝ
            (wz1PaperDirection coarse - wz1PaperDirection fine) normal := by
    rw [inner_sub_left]
    ring
  rw [hdecomp]
  calc
    |inner ℝ (wz1PaperDirection fine) normal +
        inner ℝ
          (wz1PaperDirection coarse - wz1PaperDirection fine) normal|
        ≤ |inner ℝ (wz1PaperDirection fine) normal| +
            |inner ℝ
              (wz1PaperDirection coarse - wz1PaperDirection fine) normal| :=
          abs_add_le _ _
    _ ≤ incidence + rho / 2 := add_le_add hfine hdiff

/-- Raw tube directions and paper-oriented directions have the same absolute
inner product. -/
lemma abs_inner_raw_eq_paperDirection
    {delta : ℝ} (tube : Kakeya.DeltaTube delta) (normal : Point3) :
    |inner ℝ tube.direction normal| =
      |inner ℝ (wz1PaperDirection tube) normal| := by
  rcases PureWZ2.paperDirection_sign tube with ⟨sign, hsign, hdirection⟩
  rw [hdirection, inner_smul_left]
  rcases hsign with rfl | rfl <;> simp

/-- Raw and paper-oriented cross products have the same norm. -/
lemma raw_cross_norm_eq_paper_cross_norm
    {delta : ℝ} (first second : Kakeya.DeltaTube delta) :
    ‖wz1Cross first.direction second.direction‖ =
      ‖wz1Cross (wz1PaperDirection first)
        (wz1PaperDirection second)‖ := by
  rcases PureWZ2.paperDirection_sign first with
    ⟨firstSign, hfirstSign, hfirst⟩
  rcases PureWZ2.paperDirection_sign second with
    ⟨secondSign, hsecondSign, hsecond⟩
  rw [hfirst, hsecond]
  exact PureWZ2.crossNorm_sign_invariant
    (wz1PaperDirection first) (wz1PaperDirection second)
    firstSign secondSign hfirstSign hsecondSign

/-- The selected normalized raw cross is exactly orthogonal to its first
selected raw direction. -/
lemma narrowSelection_normal_first_inner_zero
    {delta kappa : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {S : WZ1PaperTubeShading F}
    (selection : PaperWZ1NarrowDirectionSelection S kappa)
    (p : Point3) :
    inner ℝ (F.tube (selection.first p)).direction (selection.normal p) = 0 := by
  let u := (F.tube (selection.first p)).direction
  let v := (F.tube (selection.second p)).direction
  have horthogonal : inner ℝ u (wz1Cross u v) = 0 := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    have hstar : star (u : Fin 3 → ℝ) = (u : Fin 3 → ℝ) := by
      ext i
      simp
    rw [hstar, dotProduct_comm]
    exact dot_self_cross (u : Fin 3 → ℝ) (v : Fin 3 → ℝ)
  change inner ℝ u ((‖wz1Cross u v‖)⁻¹ • wz1Cross u v) = 0
  rw [inner_smul_right, horthogonal, mul_zero]

/-- The selected normalized raw cross is exactly orthogonal to its second
selected raw direction. -/
lemma narrowSelection_normal_second_inner_zero
    {delta kappa : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {S : WZ1PaperTubeShading F}
    (selection : PaperWZ1NarrowDirectionSelection S kappa)
    (p : Point3) :
    inner ℝ (F.tube (selection.second p)).direction (selection.normal p) = 0 := by
  let u := (F.tube (selection.first p)).direction
  let v := (F.tube (selection.second p)).direction
  have horthogonal : inner ℝ v (wz1Cross u v) = 0 := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    have hstar : star (v : Fin 3 → ℝ) = (v : Fin 3 → ℝ) := by
      ext i
      simp
    rw [hstar, dotProduct_comm]
    exact dot_cross_self (u : Fin 3 → ℝ) (v : Fin 3 → ℝ)
  change inner ℝ v ((‖wz1Cross u v‖)⁻¹ • wz1Cross u v) = 0
  rw [inner_smul_right, horthogonal, mul_zero]

/-- Common-parent-pair variation with an explicit constant.

This is the geometric conclusion used after the cellwise parent-pair and
orientation pigeonholes. -/
lemma paper_planeMap_variation_from_common_parent_pair
    {incidence coarseKappa : ℝ}
    {coarseFirst coarseSecond w₁ w₂ : Point3}
    (hcoarseKappa : 0 < coarseKappa)
    (hincidence : 0 ≤ incidence)
    (hfirstUnit : ‖coarseFirst‖ = 1)
    (hsecondUnit : ‖coarseSecond‖ = 1)
    (htransverse :
      coarseKappa ≤ ‖wz1Cross coarseFirst coarseSecond‖)
    (hw₁Unit : ‖w₁‖ = 1)
    (hw₂Unit : ‖w₂‖ = 1)
    (hfirst₁ : |inner ℝ coarseFirst w₁| ≤ incidence)
    (hsecond₁ : |inner ℝ coarseSecond w₁| ≤ incidence)
    (hfirst₂ : |inner ℝ coarseFirst w₂| ≤ incidence)
    (hsecond₂ : |inner ℝ coarseSecond w₂| ≤ incidence)
    (horient₁ : 0 ≤ inner ℝ (wz1Cross coarseFirst coarseSecond) w₁)
    (horient₂ : 0 ≤ inner ℝ (wz1Cross coarseFirst coarseSecond) w₂) :
    dist w₁ w₂ ≤ 6 * incidence / coarseKappa := by
  rw [dist_eq_norm]
  exact direction_overlap_lemma
    hcoarseKappa hincidence hfirstUnit hsecondUnit htransverse
    hw₁Unit hw₂Unit hfirst₁ hsecond₁ hfirst₂ hsecond₂ horient₁ horient₂

/-- Paper-normalized one-scale variation once the explicit constants fit. -/
lemma paper_planeMap_variation_le_two_rho
    {rho incidence coarseKappa : ℝ}
    {coarseFirst coarseSecond w₁ w₂ : Point3}
    (hcoarseKappa : 0 < coarseKappa)
    (hincidence : 0 ≤ incidence)
    (hbudget : 6 * incidence / coarseKappa ≤ 2 * rho)
    (hfirstUnit : ‖coarseFirst‖ = 1)
    (hsecondUnit : ‖coarseSecond‖ = 1)
    (htransverse :
      coarseKappa ≤ ‖wz1Cross coarseFirst coarseSecond‖)
    (hw₁Unit : ‖w₁‖ = 1)
    (hw₂Unit : ‖w₂‖ = 1)
    (hfirst₁ : |inner ℝ coarseFirst w₁| ≤ incidence)
    (hsecond₁ : |inner ℝ coarseSecond w₁| ≤ incidence)
    (hfirst₂ : |inner ℝ coarseFirst w₂| ≤ incidence)
    (hsecond₂ : |inner ℝ coarseSecond w₂| ≤ incidence)
    (horient₁ : 0 ≤ inner ℝ (wz1Cross coarseFirst coarseSecond) w₁)
    (horient₂ : 0 ≤ inner ℝ (wz1Cross coarseFirst coarseSecond) w₂) :
    dist w₁ w₂ ≤ 2 * rho :=
  (paper_planeMap_variation_from_common_parent_pair
    hcoarseKappa hincidence hfirstUnit hsecondUnit htransverse
    hw₁Unit hw₂Unit hfirst₁ hsecond₁ hfirst₂ hsecond₂
    horient₁ horient₂).trans hbudget

/-- The cover-specialized one-scale estimate for two points.

At each point, the supplied fine pair lies in the same two complete parent
fibers.  Thus the fine incidence bounds transfer to one common coarse pair.
After orienting both plane-map values to the same side of that pair, their
distance is at most `2 * rho` whenever the displayed constant budget holds.
-/
lemma paper_planeMap_variation_of_common_covered_fine_pairs
    {delta rho fineKappa : ℝ}
    {fineFirst₁ fineSecond₁ fineFirst₂ fineSecond₂ :
      Kakeya.DeltaTube delta}
    {coarseFirst coarseSecond : Kakeya.DeltaTube rho}
    {w₁ w₂ : Point3}
    (hfirst₁Cover : WZ1PaperTubeCovers fineFirst₁ coarseFirst)
    (hsecond₁Cover : WZ1PaperTubeCovers fineSecond₁ coarseSecond)
    (hfirst₂Cover : WZ1PaperTubeCovers fineFirst₂ coarseFirst)
    (hsecond₂Cover : WZ1PaperTubeCovers fineSecond₂ coarseSecond)
    (hfineTransverse :
      fineKappa ≤
        ‖wz1Cross (wz1PaperDirection fineFirst₁)
          (wz1PaperDirection fineSecond₁)‖)
    (hcoarseKappa : 0 < fineKappa - rho)
    (hincidence : 0 ≤ delta)
    (hrho : 0 ≤ rho)
    (hbudget : 6 * (delta + rho / 2) / (fineKappa - rho) ≤ 2 * rho)
    (hw₁Unit : ‖w₁‖ = 1)
    (hw₂Unit : ‖w₂‖ = 1)
    (hfirst₁Inc :
      |inner ℝ (wz1PaperDirection fineFirst₁) w₁| ≤ delta)
    (hsecond₁Inc :
      |inner ℝ (wz1PaperDirection fineSecond₁) w₁| ≤ delta)
    (hfirst₂Inc :
      |inner ℝ (wz1PaperDirection fineFirst₂) w₂| ≤ delta)
    (hsecond₂Inc :
      |inner ℝ (wz1PaperDirection fineSecond₂) w₂| ≤ delta)
    (horient₁ :
      0 ≤ inner ℝ
        (wz1Cross (wz1PaperDirection coarseFirst)
          (wz1PaperDirection coarseSecond)) w₁)
    (horient₂ :
      0 ≤ inner ℝ
        (wz1Cross (wz1PaperDirection coarseFirst)
          (wz1PaperDirection coarseSecond)) w₂) :
    dist w₁ w₂ ≤ 2 * rho := by
  have hcoarseTransverse :
      fineKappa - rho ≤
        ‖wz1Cross (wz1PaperDirection coarseFirst)
          (wz1PaperDirection coarseSecond)‖ :=
    paper_cover_parent_pair_transverse
      hfirst₁Cover hsecond₁Cover hfineTransverse
  have hcoarseFirst₁ :
      |inner ℝ (wz1PaperDirection coarseFirst) w₁| ≤ delta + rho / 2 :=
    paper_cover_parent_incidence hfirst₁Cover hw₁Unit hfirst₁Inc
  have hcoarseSecond₁ :
      |inner ℝ (wz1PaperDirection coarseSecond) w₁| ≤ delta + rho / 2 :=
    paper_cover_parent_incidence hsecond₁Cover hw₁Unit hsecond₁Inc
  have hcoarseFirst₂ :
      |inner ℝ (wz1PaperDirection coarseFirst) w₂| ≤ delta + rho / 2 :=
    paper_cover_parent_incidence hfirst₂Cover hw₂Unit hfirst₂Inc
  have hcoarseSecond₂ :
      |inner ℝ (wz1PaperDirection coarseSecond) w₂| ≤ delta + rho / 2 :=
    paper_cover_parent_incidence hsecond₂Cover hw₂Unit hsecond₂Inc
  exact paper_planeMap_variation_le_two_rho
    hcoarseKappa (add_nonneg hincidence (by positivity)) hbudget
    (wz1PaperDirection_norm coarseFirst)
    (wz1PaperDirection_norm coarseSecond)
    hcoarseTransverse hw₁Unit hw₂Unit
    hcoarseFirst₁ hcoarseSecond₁ hcoarseFirst₂ hcoarseSecond₂
    horient₁ horient₂

end Kakeya.Assouad

end

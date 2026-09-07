import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperUnitRescalingBasics
import MyLeanRepo.Kakeya.Assouad.WZ1.Factor2Packing
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.OneScaleVariationGeometry

/-!
# Paper-direction alignment from ordinary carrier containment

Definition 2.12 stores ordinary unit-segment carrier containment rather than
the Section 6 line-cover relation.  The standard containment-alignment lemma
still gives projective raw-direction control.  At radius below `1/8`, the
fine tube's positive vertical paper chart alone rules out the wrong antipodal
branch and turns this into ordinary paper-direction control with constant `4`.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open RealInnerProductSpace

private lemma coordinate_abs_le_norm (vector : Point3) (coordinate : Fin 3) :
    |vector coordinate| ≤ ‖vector‖ := by
  simpa [Real.norm_eq_abs] using PiLp.norm_apply_le vector coordinate

/-- Strict ordinary containment aligns the positively oriented paper
directions once the parent radius is below the antipodal threshold. -/
lemma paper_direction_alignment_of_carrier_subset
    {delta rho : ℝ}
    {fine : Kakeya.DeltaTube delta}
    {parent : Kakeya.DeltaTube rho}
    (hdelta : 0 ≤ delta) (hrho : 0 < rho) (hrhoSmall : rho < 1 / 8)
    (hfine : WZ1PaperTubeInLineClass fine)
    (hcontained : fine.carrier ⊆ parent.carrier) :
    ‖wz1PaperDirection fine - wz1PaperDirection parent‖ ≤ 4 * rho := by
  rcases containment_alignment_bound hdelta hrho fine parent hcontained with
    hsame | hopposite
  · by_cases hf : 0 ≤ fine.direction (2 : Fin 3)
    · by_cases hp : 0 ≤ parent.direction (2 : Fin 3)
      · simpa [wz1PaperDirection, hf, hp] using hsame.1
      · have hfVertical : (1 / 2 : ℝ) ≤ fine.direction (2 : Fin 3) := by
          simpa [wz1PaperDirection, hf] using hfine.1
        have hcoordinate : (1 / 2 : ℝ) ≤
            |(fine.direction - parent.direction) (2 : Fin 3)| := by
          simp only [PiLp.sub_apply]
          rw [abs_of_nonneg (by linarith)]
          linarith
        have hnorm : (1 / 2 : ℝ) ≤ ‖fine.direction - parent.direction‖ :=
          hcoordinate.trans (coordinate_abs_le_norm _ _)
        linarith [hsame.1]
    · by_cases hp : 0 ≤ parent.direction (2 : Fin 3)
      · have hfVertical : fine.direction (2 : Fin 3) ≤ -(1 / 2 : ℝ) := by
          have hpaper : (1 / 2 : ℝ) ≤ -fine.direction (2 : Fin 3) := by
            simpa [wz1PaperDirection, hf] using hfine.1
          linarith
        have hcoordinate : (1 / 2 : ℝ) ≤
            |(fine.direction - parent.direction) (2 : Fin 3)| := by
          simp only [PiLp.sub_apply]
          rw [abs_of_nonpos (by linarith)]
          linarith
        have hnorm : (1 / 2 : ℝ) ≤ ‖fine.direction - parent.direction‖ :=
          hcoordinate.trans (coordinate_abs_le_norm _ _)
        linarith [hsame.1]
      · have hfPaper : wz1PaperDirection fine = -fine.direction := by
          rw [wz1PaperDirection, if_neg hf]
        have hpPaper : wz1PaperDirection parent = -parent.direction := by
          rw [wz1PaperDirection, if_neg hp]
        rw [hfPaper, hpPaper]
        calc
          ‖-fine.direction - -parent.direction‖ =
              ‖-(fine.direction - parent.direction)‖ := by congr 1 <;> module
          _ = ‖fine.direction - parent.direction‖ := norm_neg _
          _ ≤ 4 * rho := hsame.1
  · by_cases hf : 0 ≤ fine.direction (2 : Fin 3)
    · by_cases hp : 0 ≤ parent.direction (2 : Fin 3)
      · have hfVertical : (1 / 2 : ℝ) ≤ fine.direction (2 : Fin 3) := by
          simpa [wz1PaperDirection, hf] using hfine.1
        have hcoordinate : (1 / 2 : ℝ) ≤
            |(fine.direction + parent.direction) (2 : Fin 3)| := by
          simp only [PiLp.add_apply]
          rw [abs_of_nonneg (by linarith)]
          linarith
        have hnorm : (1 / 2 : ℝ) ≤ ‖fine.direction + parent.direction‖ :=
          hcoordinate.trans (coordinate_abs_le_norm _ _)
        linarith [hopposite.1]
      · simpa [wz1PaperDirection, hf, hp, sub_neg_eq_add] using hopposite.1
    · by_cases hp : 0 ≤ parent.direction (2 : Fin 3)
      · have hfPaper : wz1PaperDirection fine = -fine.direction := by
          rw [wz1PaperDirection, if_neg hf]
        have hpPaper : wz1PaperDirection parent = parent.direction := by
          rw [wz1PaperDirection, if_pos hp]
        rw [hfPaper, hpPaper]
        calc
          ‖-fine.direction - parent.direction‖ =
              ‖-(fine.direction + parent.direction)‖ := by congr 1 <;> module
          _ = ‖fine.direction + parent.direction‖ := norm_neg _
          _ ≤ 4 * rho := hopposite.1
      · have hfVertical : fine.direction (2 : Fin 3) ≤ -(1 / 2 : ℝ) := by
          have hpaper : (1 / 2 : ℝ) ≤ -fine.direction (2 : Fin 3) := by
            simpa [wz1PaperDirection, hf] using hfine.1
          linarith
        have hcoordinate : (1 / 2 : ℝ) ≤
            |(fine.direction + parent.direction) (2 : Fin 3)| := by
          simp only [PiLp.add_apply]
          rw [abs_of_nonpos (by linarith)]
          linarith
        have hnorm : (1 / 2 : ℝ) ≤ ‖fine.direction + parent.direction‖ :=
          hcoordinate.trans (coordinate_abs_le_norm _ _)
        linarith [hopposite.1]

/-- Family-level form for the parent canonically derived from one pure scale
cover. -/
lemma WZ2PaperPureScaleCoverData.paper_parent_direction_alignment
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    (data : WZ2PaperPureScaleCoverData fine rho C)
    (hrhoSmall : rho < 1 / 8)
    (hfine : WZ1PaperIsLineClass fine)
    (source : Fin fine.card) :
    ‖wz1PaperDirection (fine.tube source) -
        wz1PaperDirection (data.coarse.tube (data.cover.parent source))‖ ≤
      4 * rho := by
  apply paper_direction_alignment_of_carrier_subset
    data.delta_pos.le data.rho_pos hrhoSmall
    (hfine source)
  exact (mem_wz2PaperOrdinaryFullFiberIndices_iff
    (data.cover.parent source) source).mp
    (data.cover.parent_mem_fullFiber source)

/-- A transverse fine pair remains transverse after passage to its two pure
strict-carrier parents, with the explicit `8 * rho` loss. -/
lemma pure_carrier_parent_pair_transverse
    {delta rho kappa : ℝ}
    {fineFirst fineSecond : Kakeya.DeltaTube delta}
    {coarseFirst coarseSecond : Kakeya.DeltaTube rho}
    (hdelta : 0 ≤ delta) (hrho : 0 < rho) (hrhoSmall : rho < 1 / 8)
    (hfineFirst : WZ1PaperTubeInLineClass fineFirst)
    (hfineSecond : WZ1PaperTubeInLineClass fineSecond)
    (hfirst : fineFirst.carrier ⊆ coarseFirst.carrier)
    (hsecond : fineSecond.carrier ⊆ coarseSecond.carrier)
    (htransverse : kappa ≤
      ‖wz1Cross (wz1PaperDirection fineFirst)
        (wz1PaperDirection fineSecond)‖) :
    kappa - 8 * rho ≤
      ‖wz1Cross (wz1PaperDirection coarseFirst)
        (wz1PaperDirection coarseSecond)‖ := by
  have hfirstAlign := paper_direction_alignment_of_carrier_subset
    hdelta hrho hrhoSmall hfineFirst hfirst
  have hsecondAlign := paper_direction_alignment_of_carrier_subset
    hdelta hrho hrhoSmall hfineSecond hsecond
  have hdiff := wz1Cross_sub_norm_le_of_unit
    (wz1PaperDirection_norm fineFirst)
    (wz1PaperDirection_norm fineSecond)
    (wz1PaperDirection_norm coarseFirst)
    (wz1PaperDirection_norm coarseSecond)
    hfirstAlign hsecondAlign
  have hnorm :
      ‖wz1Cross (wz1PaperDirection fineFirst)
          (wz1PaperDirection fineSecond)‖ ≤
        ‖wz1Cross (wz1PaperDirection coarseFirst)
          (wz1PaperDirection coarseSecond)‖ + 8 * rho := by
    calc
      ‖wz1Cross (wz1PaperDirection fineFirst)
          (wz1PaperDirection fineSecond)‖ ≤
          ‖wz1Cross (wz1PaperDirection fineFirst)
              (wz1PaperDirection fineSecond) -
            wz1Cross (wz1PaperDirection coarseFirst)
              (wz1PaperDirection coarseSecond)‖ +
            ‖wz1Cross (wz1PaperDirection coarseFirst)
              (wz1PaperDirection coarseSecond)‖ :=
        norm_le_norm_sub_add _ _
      _ ≤ 8 * rho +
          ‖wz1Cross (wz1PaperDirection coarseFirst)
            (wz1PaperDirection coarseSecond)‖ := by
        have hdiff' :
            ‖wz1Cross (wz1PaperDirection fineFirst)
                (wz1PaperDirection fineSecond) -
              wz1Cross (wz1PaperDirection coarseFirst)
                (wz1PaperDirection coarseSecond)‖ ≤
              8 * rho := by
          nlinarith [hdiff]
        exact add_le_add hdiff' (le_refl _)
      _ = _ := by ring
  linarith

/-- A fine plane-incidence bound transfers to an ordinary strict-carrier
parent, paying the same `4 * rho` direction loss. -/
lemma pure_carrier_parent_incidence
    {delta rho incidence : ℝ}
    {fine : Kakeya.DeltaTube delta}
    {coarse : Kakeya.DeltaTube rho}
    {normal : Point3}
    (hdelta : 0 ≤ delta) (hrho : 0 < rho) (hrhoSmall : rho < 1 / 8)
    (hfineLine : WZ1PaperTubeInLineClass fine)
    (hcontained : fine.carrier ⊆ coarse.carrier)
    (hnormal : ‖normal‖ = 1)
    (hfine : |inner ℝ (wz1PaperDirection fine) normal| ≤ incidence) :
    |inner ℝ (wz1PaperDirection coarse) normal| ≤ incidence + 4 * rho := by
  have halign := paper_direction_alignment_of_carrier_subset
    hdelta hrho hrhoSmall hfineLine hcontained
  have hdiff :
      |inner ℝ
        (wz1PaperDirection coarse - wz1PaperDirection fine) normal| ≤
        4 * rho := by
    calc
      |inner ℝ
          (wz1PaperDirection coarse - wz1PaperDirection fine) normal| ≤
          ‖wz1PaperDirection coarse - wz1PaperDirection fine‖ *
            ‖normal‖ := abs_real_inner_le_norm _ _
      _ = ‖wz1PaperDirection coarse - wz1PaperDirection fine‖ := by
        rw [hnormal, mul_one]
      _ = ‖wz1PaperDirection fine - wz1PaperDirection coarse‖ :=
        norm_sub_rev _ _
      _ ≤ 4 * rho := halign
  rw [show inner ℝ (wz1PaperDirection coarse) normal =
      inner ℝ (wz1PaperDirection fine) normal +
        inner ℝ
          (wz1PaperDirection coarse - wz1PaperDirection fine) normal by
    rw [inner_sub_left] <;> ring]
  exact (abs_add_le _ _).trans (add_le_add hfine hdiff)

end Kakeya.Assouad.PureWZ2

end

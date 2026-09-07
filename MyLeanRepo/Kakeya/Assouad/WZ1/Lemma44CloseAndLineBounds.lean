import MyLeanRepo.Kakeya.Assouad.WZ1.ProjectionTheoremFirstLayerStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.NonConcentrationToThinTubes
import MyLeanRepo.Kakeya.Assouad.WZ1.AngleGeometryBase

/-!
# WZ1 Lemma 44: close-pair and near-line bounds

These are the first two terms in the three-case upper bound for the number of
bad-pair triples.
-/

noncomputable section

namespace Kakeya.Assouad

open scoped ENNReal

attribute [local instance] Classical.propDecidable

lemma lineThrough_direction {p q : Point2} (hne : p ≠ q) :
    Module.finrank ℝ (lineThrough p q).direction = 1 := by
  have h1 : q - p ≠ 0 := by
    intro h
    exact hne (sub_eq_zero.mp h).symm
  have h2 :
      (lineThrough p q).direction = ℝ ∙ (q - p) := by
    simp [lineThrough, AffineSubspace.direction_mk']
  rw [h2]
  exact finrank_span_singleton h1

private lemma sum_const_ennreal
    {α : Type*} {s : Finset α} {c : ENNReal} :
    ∑ _x ∈ s, c = (s.card : ENNReal) * c := by
  rw [Finset.sum_const]
  simp [nsmul_eq_mul]

/-- Case 1: triples for which the two `G₁` points are `D`-close. -/
lemma threeCase_case1
    {delta D : ℝ} (_hdelta : 0 < delta)
    (hD : delta ≤ D) (hD1 : D ≤ 1)
    {G1 G2 : DiscreteSet 2} (C_F : ENNReal)
    (hFrost1 : G1.IsFrostman delta 1 C_F) :
    ∑ b1 ∈ G1,
        ((G1.filter fun b1' =>
          dist b1 b1' ≤ D).card : ENNReal) *
          G2.enncard ≤
      C_F * Kakeya.realRpowENN D 1 *
        G1.enncard * G1.enncard * G2.enncard := by
  let X : ENNReal :=
    C_F * Kakeya.realRpowENN D 1
  have h_main :
      ∀ b1 ∈ G1,
        ((G1.filter fun b1' =>
          dist b1 b1' ≤ D).card : ENNReal) ≤
          X * G1.enncard := by
    intro b1 _
    have h_eq :
        (G1.filter fun b1' => dist b1 b1' ≤ D) =
          G1.filter fun y => dist y b1 ≤ D := by
      ext x
      simp [dist_comm]
    rw [h_eq]
    simpa [DiscreteSet.ballCount, X] using
      hFrost1 b1 D hD hD1
  have h_each :
      ∀ b1 ∈ G1,
        ((G1.filter fun b1' =>
          dist b1 b1' ≤ D).card : ENNReal) *
            G2.enncard ≤
          X * G1.enncard * G2.enncard := by
    intro b1 hb1
    calc
      ((G1.filter fun b1' =>
          dist b1 b1' ≤ D).card : ENNReal) *
            G2.enncard
          ≤ (X * G1.enncard) * G2.enncard := by
            gcongr
            exact h_main b1 hb1
      _ = X * G1.enncard * G2.enncard := by
        simp [mul_assoc]
  have h_sum :
      ∑ b1 ∈ G1,
          ((G1.filter fun b1' =>
            dist b1 b1' ≤ D).card : ENNReal) *
            G2.enncard ≤
        ∑ _b1 ∈ G1,
          X * G1.enncard * G2.enncard :=
    Finset.sum_le_sum h_each
  rw [sum_const_ennreal] at h_sum
  simpa [X, DiscreteSet.enncard, mul_assoc,
    mul_comm, mul_left_comm] using h_sum

/-- Case 2 for one pair: points close to the line through the pair. -/
lemma threeCase_case2_perPair
    {delta lambda zeta s : ℝ}
    (hdelta : 0 < delta)
    (_hlambda : 0 < lambda) (_hzeta : 0 < zeta)
    (hs : delta ≤ s) (hs1 : s ≤ 1)
    {G2 : DiscreteSet 2}
    (hNonConc :
      WZ1LineNonConcentration
        delta lambda zeta G2)
    {b1 b1' : Point2} (hne : b1 ≠ b1') :
    ((G2.filter fun b2 =>
        b2 ∈ Metric.thickening s
          ((lineThrough b1 b1') : Set Point2)).card :
      ENNReal) ≤
      Kakeya.realRpowENN
          (Real.rpow delta (-lambda) * s) zeta *
        G2.enncard := by
  have hfin :
      Module.finrank ℝ
        (lineThrough b1 b1').direction = 1 :=
    lineThrough_direction hne
  obtain ⟨normal, hnormal, horthogonal⟩ :=
    exists_unit_normal_of_finrank_one hfin
  let offset : ℝ := inner ℝ b1 normal
  have hb1 :
      b1 ∈ (lineThrough b1 b1' : Set Point2) :=
    lineThrough_contains_first
  have hs_pos : 0 < s := hdelta.trans_le hs
  have h_strip :
      Metric.thickening s
          ((lineThrough b1 b1') : Set Point2) ⊆
        {y : Point2 |
          |inner ℝ y normal - offset| ≤ s} :=
    thickening_subset_strip hfin normal hnormal
      horthogonal b1 hb1 s hs_pos
  have h_filter :
      (G2.filter fun b2 =>
          b2 ∈ Metric.thickening s
            ((lineThrough b1 b1') : Set Point2)) ⊆
        G2.filter fun y =>
          |inner ℝ y normal - offset| ≤ s := by
    intro b2 hb2
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hb2).1,
        h_strip (Finset.mem_filter.mp hb2).2⟩
  have h_card :
      ((G2.filter fun b2 =>
          b2 ∈ Metric.thickening s
            ((lineThrough b1 b1') : Set Point2)).card :
        ENNReal) ≤
        ((G2.filter fun y =>
          |inner ℝ y normal - offset| ≤ s).card :
          ENNReal) := by
    exact_mod_cast Finset.card_le_card h_filter
  exact h_card.trans
    (hNonConc normal hnormal offset s hs hs1)

/-- Case 2 summed over all ordered distinct pairs in `G₁`. -/
lemma threeCase_case2
    {delta lambda zeta s : ℝ}
    (hdelta : 0 < delta)
    (hlambda : 0 < lambda) (hzeta : 0 < zeta)
    (hs : delta ≤ s) (hs1 : s ≤ 1)
    {G1 G2 : DiscreteSet 2}
    (hNonConc :
      WZ1LineNonConcentration
        delta lambda zeta G2) :
    ∑ b1 ∈ G1, ∑ b1' ∈ G1.erase b1,
        ((G2.filter fun b2 =>
          b2 ∈ Metric.thickening s
            ((lineThrough b1 b1') : Set Point2)).card :
          ENNReal) ≤
      Kakeya.realRpowENN
          (Real.rpow delta (-lambda) * s) zeta *
        G1.enncard * G1.enncard * G2.enncard := by
  let bound : ENNReal :=
    Kakeya.realRpowENN
        (Real.rpow delta (-lambda) * s) zeta *
      G2.enncard
  have h_pair :
      ∀ b1 ∈ G1, ∀ b1' ∈ G1.erase b1,
        ((G2.filter fun b2 =>
          b2 ∈ Metric.thickening s
            ((lineThrough b1 b1') : Set Point2)).card :
          ENNReal) ≤ bound := by
    intro b1 _ b1' hb1'
    have hne : b1 ≠ b1' :=
      (Finset.mem_erase.mp hb1').1.symm
    exact threeCase_case2_perPair
      hdelta hlambda hzeta hs hs1 hNonConc hne
  have h_inner :
      ∀ b1 ∈ G1,
        ∑ b1' ∈ G1.erase b1,
            ((G2.filter fun b2 =>
              b2 ∈ Metric.thickening s
                ((lineThrough b1 b1') :
                  Set Point2)).card : ENNReal) ≤
          G1.enncard * bound := by
    intro b1 hb1
    calc
      ∑ b1' ∈ G1.erase b1,
          ((G2.filter fun b2 =>
            b2 ∈ Metric.thickening s
              ((lineThrough b1 b1') :
                Set Point2)).card : ENNReal)
          ≤ ∑ _b1' ∈ G1.erase b1, bound :=
            Finset.sum_le_sum
              (fun b1' hb1' =>
                h_pair b1 hb1 b1' hb1')
      _ ≤ ∑ _b1' ∈ G1, bound :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.erase_subset b1 G1)
          (fun _ _ => by simp)
      _ = G1.enncard * bound := by
        rw [sum_const_ennreal,
          DiscreteSet.enncard]
  have h_sum :
      ∑ b1 ∈ G1, ∑ b1' ∈ G1.erase b1,
          ((G2.filter fun b2 =>
            b2 ∈ Metric.thickening s
              ((lineThrough b1 b1') :
                Set Point2)).card : ENNReal) ≤
        ∑ _b1 ∈ G1, G1.enncard * bound :=
    Finset.sum_le_sum h_inner
  rw [sum_const_ennreal] at h_sum
  simpa [bound, DiscreteSet.enncard, mul_assoc,
    mul_comm, mul_left_comm] using h_sum

end Kakeya.Assouad

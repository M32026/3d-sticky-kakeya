import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCarrierVolumeLower
import MyLeanRepo.Kakeya.Assouad.TubeVolumeLowerBound
import Mathlib.Tactic

/-!
# Body volume positivity and mass finiteness for paper tube families

Three reusable lemmas needed by the Strategy3MultiScale `hmass_band` argument:

1. `paper_body_family_mass_positive`: the body family mass is strictly positive
   when the family is nonempty and line-class.
2. `paper_shading_mass_positive`: a dense shading has strictly positive mass.
3. `paper_shading_mass_ne_top`: any paper shading has finite mass, because every
   carrier is contained in `axisBox 2 2 2` (volume 8).

These are extracted from patterns in `FiberScaleWeakMap.lean` and
`DilateMildRescale.lean`.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set Finset Classical ENNReal
open scoped ENNReal

attribute [local instance] Classical.propDecidable

/-- The body family of a nonempty line-class tube family has positive mass.

Each paper tube carrier contains a canonical δ-tube (for δ ≤ 1/12), and every
δ-tube has volume at least δ². Since the family is nonempty, at least one
carrier contributes positive volume. -/
lemma paper_body_family_mass_positive
    {epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily epsilon}
    (hepsilon_pos : 0 < epsilon)
    (hepsilon_small : epsilon ≤ 1 / 12)
    (hline_class : WZ1PaperIsLineClass F)
    (hF_nonempty : F.Nonempty) :
    0 < (wz1PaperBodyFamily F).mass := by
  have hcard_pos : 0 < F.card := hF_nonempty
  let i : Fin F.card := ⟨0, hcard_pos⟩
  have h1 : WZ1PaperTubeInLineClass (F.tube i) := hline_class i
  have h2 : Kakeya.deltaTubeVolume epsilon ≤
      volume (wz1PaperTubeCarrier (F.tube i)) :=
    wz2PaperTubeCarrier_volume_lower hepsilon_pos hepsilon_small (F.tube i) h1
  have h3 : ENNReal.ofReal (epsilon ^ 2) ≤ Kakeya.deltaTubeVolume epsilon :=
    canonical_volume_lower hepsilon_pos
  have h4 : 0 < ENNReal.ofReal (epsilon ^ 2) := by
    exact ENNReal.ofReal_pos.mpr (by positivity)
  have h5 : 0 < volume (wz1PaperTubeCarrier (F.tube i)) :=
    h4.trans_le (h3.trans h2)
  have h6 : (wz1PaperBodyFamily F).mass =
      ∑ j : Fin F.card, volume (wz1PaperTubeCarrier (F.tube j)) := by rfl
  rw [h6]
  have h7 : 0 < ∑ j : Fin F.card, volume (wz1PaperTubeCarrier (F.tube j)) := by
    have h_le : volume (wz1PaperTubeCarrier (F.tube i)) ≤
        ∑ j : Fin F.card, volume (wz1PaperTubeCarrier (F.tube j)) := by
      have h_sub : ({i} : Finset (Fin F.card)) ⊆ Finset.univ := by simp
      have h_sum : ∑ j ∈ ({i} : Finset (Fin F.card)), volume (wz1PaperTubeCarrier (F.tube j)) =
          volume (wz1PaperTubeCarrier (F.tube i)) := by simp
      rw [← h_sum]
      apply Finset.sum_le_sum_of_subset_of_nonneg h_sub
      intro j _ _; positivity
    exact h5.trans_le h_le
  exact h7

/-- A shading satisfying the density condition has positive mass.

Uses `paper_body_family_mass_positive` and the fact that the density factor
`ε^loss` is positive. -/
lemma paper_shading_mass_positive
    {epsilon loss : ℝ}
    {F : Kakeya.Streamlined.TubeFamily epsilon}
    {S : WZ1PaperTubeShading F}
    (hepsilon_pos : 0 < epsilon)
    (hepsilon_small : epsilon ≤ 1 / 12)
    (hline_class : WZ1PaperIsLineClass F)
    (hF_nonempty : F.Nonempty)
    (hdense : Kakeya.realRpowENN epsilon loss * (wz1PaperBodyFamily F).mass ≤ S.mass) :
    0 < S.mass := by
  have h_eps_loss_pos : 0 < epsilon ^ loss := Real.rpow_pos_of_pos hepsilon_pos loss
  have h1 : 0 < Kakeya.realRpowENN epsilon loss := by
    simp [Kakeya.realRpowENN, ENNReal.ofReal_pos, h_eps_loss_pos]
  have h2 : 0 < (wz1PaperBodyFamily F).mass :=
    paper_body_family_mass_positive hepsilon_pos hepsilon_small hline_class hF_nonempty
  have h3 : 0 < Kakeya.realRpowENN epsilon loss * (wz1PaperBodyFamily F).mass :=
    ENNReal.mul_pos h1.ne' h2.ne'
  exact h3.trans_le hdense

/-- Every paper shading has finite mass.

Each carrier `S.carrier i` is a subset of the corresponding paper tube carrier,
which is by definition a subset of `axisBox 2 2 2` (volume 8). Hence every
carrier has finite volume, and the finite sum `S.mass` is finite. -/
lemma paper_shading_mass_ne_top
    {epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily epsilon}
    {S : WZ1PaperTubeShading F} :
    S.mass ≠ ⊤ := by
  have h_sub_box : ∀ (i : Fin F.card),
      S.carrier i ⊆ Kakeya.Streamlined.axisBox 2 2 2 := by
    intro i
    let B := (wz1PaperBodyFamily F).body i
    have h3 : S.carrier i ⊆ B.carrier := S.subset_body i
    have h4 : B.carrier = wz1PaperTubeCarrier (F.tube i) := by
      simp [wz1PaperBodyFamily, B]
    have h5 : B.carrier ⊆ Kakeya.Streamlined.axisBox 2 2 2 := by
      rw [h4]
      have h51 : wz1PaperTubeCarrier (F.tube i) ⊆ Kakeya.Streamlined.axisBox 2 2 2 := by
        simp [wz1PaperTubeCarrier]
      exact h51

    exact Set.Subset.trans h3 h5
  have h_box_fin : volume (Kakeya.Streamlined.axisBox 2 2 2) ≠ ⊤ := by
    rw [Kakeya.Streamlined.volume_axisBox 2 2 2 (by norm_num) (by norm_num) (by norm_num)]
    exact ENNReal.ofReal_ne_top
  have h : ∀ (i : Fin F.card), volume (S.carrier i) ≠ ⊤ := by
    intro i
    have h6 : volume (S.carrier i) ≤ volume (Kakeya.Streamlined.axisBox 2 2 2) :=
      measure_mono (h_sub_box i)
    exact ne_top_of_le_ne_top h_box_fin h6
  rw [Kakeya.Streamlined.Shading.mass]
  exact ENNReal.sum_ne_top.mpr (fun i _ => h i)

end Kakeya.Assouad

end

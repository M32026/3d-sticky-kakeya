import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.RobustCloseCountPhase4
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.RobustCloseCountPhase5
import Mathlib.Tactic

/-!
# Transverse-pair condition from balanced cover + robust close count

Gap lemma for the A1' plane-map construction:

Given a paper tube shading with:
1. Robust close-direction count bound ≤ R (from balanced cover + direction packing)
2. Average multiplicity lower bound A (from extremality + uniform cell mass)
3. Strict gap R < A/2

Extract a subshading Z with:
- Pointwise multiplicity ≥ m (natural number, R < m ≤ A/2)
- Transverse-pair condition at every point
- Mass retention ≥ 1/2

This wires together:
- Phase 5: `high_multiplicity_subshading` (average → pointwise multiplicity)
- Phase 4: `paper_transverse_from_close_count_lt_multiplicity` (close count + multiplicity → transverse)
- Robust close count transfer to subshadings
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set ENNReal Finset

attribute [local instance] Classical.propDecidable

/-- Close-direction count is monotone in the threshold kappa. -/
lemma close_count_monotone_kappa
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {S : WZ1PaperTubeShading F}
    {p : Point3} {i : Fin F.card}
    {kappa1 kappa2 : ℝ} (h : kappa1 ≤ kappa2) :
    paperCloseDirectionCount S p i kappa1 ≤ paperCloseDirectionCount S p i kappa2 := by
  apply Finset.card_le_card
  intro j hj
  have h1 : ‖wz1Cross (F.tube i).direction (F.tube j).direction‖ < kappa1 :=
    (Finset.mem_filter.mp hj).2.2
  have h2 : ‖wz1Cross (F.tube i).direction (F.tube j).direction‖ < kappa2 :=
    h1.trans_le h
  simp only [paperCloseDirectionCount, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  exact ⟨hj.1, h2⟩

/-- Close-direction count decreases under subshading (restricted carriers). -/
lemma close_count_subshading
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {S Z : WZ1PaperTubeShading F}
    (hsub : PaperIsSubshading Z S)
    {p : Point3} {i : Fin F.card} {kappa : ℝ} :
    paperCloseDirectionCount Z p i kappa ≤ paperCloseDirectionCount S p i kappa := by
  apply Finset.card_le_card
  intro j hj
  have hjp : p ∈ Z.carrier j := (Finset.mem_filter.mp hj).2.1
  have hjs : p ∈ S.carrier j := hsub j hjp
  have hcross : ‖wz1Cross (F.tube i).direction (F.tube j).direction‖ < kappa :=
    (Finset.mem_filter.mp hj).2.2
  simp only [paperCloseDirectionCount, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  exact ⟨hjs, hcross⟩

/-- **Gap lemma**: from robust close count + average multiplicity, produce a
subshading with the transverse-pair condition.

Given:
- Close direction count ≤ R at threshold L
- Average multiplicity ≥ A (i.e. A * volume(union) ≤ mass)
- Natural number m with R < m ≤ A/2

Produce Z ⊆ S with:
- Pointwise multiplicity ≥ m
- Transverse pair at every point (exists i,j both containing p with cross ≥ kappa)
- Mass retention ≥ 1/2

This is the key bridge from the sticky balanced cover to the per-cell plane map
selector `per_cell_plane_map_from_transverse_pair`.
-/
lemma transverse_subshading_from_close_count_and_avg
    {delta kappa L : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {S : WZ1PaperTubeShading F}
    (R A : ENNReal)
    (hR_ne_top : R ≠ ⊤)
    (hA_ne_top : A ≠ ⊤)
    (h_vol_ne_top : volume S.union ≠ ⊤)
    (h_mass_ne_top : S.mass ≠ ⊤)
    -- Robust close count at threshold L
    (hclose_L : ∀ p ∈ S.union, ∀ i, p ∈ S.carrier i →
      (paperCloseDirectionCount S p i L : ENNReal) ≤ R)
    (hkappa_le_L : kappa ≤ L)
    -- Average multiplicity bound
    (h_avg : A * volume S.union ≤ S.mass)
    -- Natural number bridge
    (m : ℕ)
    (hm_le_A2 : (m : ENNReal) ≤ A / 2)
    (hm_gt_R : R < (m : ENNReal))
    :
    ∃ (Z : WZ1PaperTubeShading F),
      PaperIsSubshading Z S ∧
      (∀ p ∈ Z.union, m ≤ Z.pointMultiplicity p) ∧
      (∀ p ∈ Z.union, ∃ (i j : Fin F.card),
        p ∈ Z.carrier i ∧ p ∈ Z.carrier j ∧
        kappa ≤ ‖wz1Cross (F.tube i).direction (F.tube j).direction‖) ∧
      (1 / 2 : ENNReal) * S.mass ≤ Z.mass := by
  -- Step 1: Extract high-multiplicity subshading (Phase 5)
  have h_main : ∃ (Z : WZ1PaperTubeShading F),
      PaperIsSubshading Z S ∧
      (∀ p ∈ Z.union, (A / 2) ≤ (Z.pointMultiplicity p : ENNReal)) ∧
      (1 / 2 : ENNReal) * S.mass ≤ Z.mass :=
    high_multiplicity_subshading A hA_ne_top h_vol_ne_top h_mass_ne_top h_avg
  rcases h_main with ⟨Z, hsub, hmult_Z, hmass_Z⟩

  -- Step 2: Convert ENNReal multiplicity bound to natural number
  have hmult_nat : ∀ p ∈ Z.union, m ≤ Z.pointMultiplicity p := by
    intro p hp
    have h1 : (A / 2 : ENNReal) ≤ (Z.pointMultiplicity p : ENNReal) := hmult_Z p hp
    have h2 : (m : ENNReal) ≤ (Z.pointMultiplicity p : ENNReal) :=
      le_trans hm_le_A2 h1
    exact_mod_cast h2

  -- Step 3: Transfer close count bound to Z and threshold kappa
  have hclose_Z : ∀ p ∈ Z.union, ∀ i, p ∈ Z.carrier i →
      paperCloseDirectionCount Z p i kappa < m := by
    intro p hp i hi
    have h_p_in_S : p ∈ S.union := by
      exact ⟨i, hsub i hi⟩
    have h1 : (paperCloseDirectionCount Z p i kappa : ENNReal) ≤
        (paperCloseDirectionCount S p i kappa : ENNReal) := by
      exact_mod_cast close_count_subshading hsub
    have h2 : (paperCloseDirectionCount S p i kappa : ENNReal) ≤
        (paperCloseDirectionCount S p i L : ENNReal) := by
      exact_mod_cast close_count_monotone_kappa hkappa_le_L
    have h3 : (paperCloseDirectionCount S p i L : ENNReal) ≤ R :=
      hclose_L p h_p_in_S i (hsub i hi)
    have h4 : (paperCloseDirectionCount Z p i kappa : ENNReal) < (m : ENNReal) :=
      h1.trans (h2.trans h3) |>.trans_lt hm_gt_R
    exact_mod_cast h4

  -- Step 4: Apply Phase 4 to get transverse condition
  have htransverse : ∀ p ∈ Z.union, ∀ i, p ∈ Z.carrier i →
      ∃ j, p ∈ Z.carrier j ∧
        kappa ≤ ‖wz1Cross (F.tube i).direction (F.tube j).direction‖ :=
    paper_transverse_from_close_count_lt_multiplicity kappa hmult_nat hclose_Z

  -- Step 5: Convert "for every i, exists j" to "exists pair (i,j)"
  have hpair : ∀ p ∈ Z.union, ∃ (i j : Fin F.card),
      p ∈ Z.carrier i ∧ p ∈ Z.carrier j ∧
      kappa ≤ ‖wz1Cross (F.tube i).direction (F.tube j).direction‖ := by
    intro p hp_union
    have h_exists : ∃ (i : Fin F.card), p ∈ Z.carrier i := by
      exact hp_union
    rcases h_exists with ⟨i, hi⟩
    have htrans : ∃ (j : Fin F.card), p ∈ Z.carrier j ∧
        kappa ≤ ‖wz1Cross (F.tube i).direction (F.tube j).direction‖ :=
      htransverse p hp_union i hi
    rcases htrans with ⟨j, hjp, hcross⟩
    exact ⟨i, j, hi, hjp, hcross⟩

  exact ⟨Z, hsub, hmult_nat, hpair, hmass_Z⟩

end Kakeya.Assouad.PureWZ2

end

import MyLeanRepo.Kakeya.Assouad.PYZInput
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterBlockCinematicStatements

/-!
WZ2 Section 7: apply the proved uniform-C2 PYZ theorem to a half-parameter
Katz--Tao set with an arbitrary fixed nonconcentration constant.
-/

namespace Kakeya.Assouad

open Kakeya.Cinematic Set Finset

attribute [local instance] Classical.propDecidable

/-- Generalized global cardinality bound from unit-ball KT at radius 1. -/
lemma unitBall_global_card_general (A : DiscreteSet 3) (w : ℝ) (hw : 0 < w) (hw_le1 : w ≤ 1)
    (C : ENNReal) (hC : 1 ≤ C) (hC_top : C ≠ ⊤)
    (hKT : A.IsKatzTao w 1 C) (hA_unit : A.IsInUnitBall) :
    (A.card : ℝ) ≤ ENNReal.toReal C / w := by
  let c := ENNReal.toReal C
  have hc_nonneg : 0 ≤ c := by positivity
  have hc_ge1 : 1 ≤ c := by
    have h1 : (1 : ENNReal) ≤ C := hC
    have h2 : ENNReal.ofReal c = C := ENNReal.ofReal_toReal hC_top
    have h3 : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal c := by
      simpa using h1.trans (le_of_eq h2.symm)
    exact (ENNReal.ofReal_le_ofReal_iff hc_nonneg).mp h3
  have hc_pos : 0 < c := by linarith
  have h1 : A.filter (fun p : Point 3 => dist p 0 ≤ 1) = A := by
    ext p
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hp, _⟩; exact hp
    · intro hp; exact ⟨hp, hA_unit p hp⟩
  have hKT' := hKT 0 1 hw_le1 (by norm_num)
  have h_eq : A.ballCount 0 1 = (A.card : ENNReal) := by
    rw [DiscreteSet.ballCount, h1]
  rw [h_eq] at hKT'
  have h_rpow : Kakeya.realRpowENN (1 / w) 1 = ENNReal.ofReal (1 / w) := by
    simp [Kakeya.realRpowENN, Real.rpow_one]
  rw [h_rpow] at hKT'
  have h_mul : C * ENNReal.ofReal (1 / w) = ENNReal.ofReal (c * (1 / w)) := by
    have h2 : C = ENNReal.ofReal c := (ENNReal.ofReal_toReal hC_top).symm
    rw [h2]
    rw [← ENNReal.ofReal_mul hc_nonneg]
  rw [h_mul] at hKT'
  have h_card_cast : (A.card : ENNReal) = ENNReal.ofReal (A.card : ℝ) := by simp
  rw [h_card_cast] at hKT'
  have h_y_pos : 0 ≤ c * (1 / w) := by positivity
  have h_iff : (ENNReal.ofReal (A.card : ℝ) ≤ ENNReal.ofReal (c * (1 / w))) ↔
      (A.card : ℝ) ≤ c * (1 / w) :=
    ENNReal.ofReal_le_ofReal_iff h_y_pos
  have h_final : (A.card : ℝ) ≤ c * (1 / w) := h_iff.mp hKT'
  have h3 : c * (1 / w) = c / w := by
    field_simp [hw.ne']
  rw [h3] at h_final
  exact h_final

/-- Half-box coordinate bounds imply membership in the unit ball. -/
lemma halfBox_implies_unitBall (points : DiscreteSet 3)
    (hbox : ∀ p ∈ points, |p 0| ≤ 1 / 2 ∧ |p 1| ≤ 1 / 2 ∧ |p 2| ≤ 1 / 2) :
    points.IsInUnitBall := by
  intro p hp
  have h1 := hbox p hp
  have h21 : |p 0| ≤ 1 / 2 := h1.1
  have h2 : (p 0)^2 ≤ 1 / 4 := by
    have h22 : -1 / 2 ≤ p 0 := by linarith [abs_le.mp h21]
    have h23 : p 0 ≤ 1 / 2 := by linarith [abs_le.mp h21]
    nlinarith
  have h31 : |p 1| ≤ 1 / 2 := h1.2.1
  have h3 : (p 1)^2 ≤ 1 / 4 := by
    have h32 : -1 / 2 ≤ p 1 := by linarith [abs_le.mp h31]
    have h33 : p 1 ≤ 1 / 2 := by linarith [abs_le.mp h31]
    nlinarith
  have h41 : |p 2| ≤ 1 / 2 := h1.2.2
  have h4 : (p 2)^2 ≤ 1 / 4 := by
    have h42 : -1 / 2 ≤ p 2 := by linarith [abs_le.mp h41]
    have h43 : p 2 ≤ 1 / 2 := by linarith [abs_le.mp h41]
    nlinarith
  have h5 : dist p 0 ^ 2 = (p 0)^2 + (p 1)^2 + (p 2)^2 := by
    simp [dist_eq_norm, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  have h6 : dist p 0 ^ 2 ≤ 1 := by
    rw [h5]; linarith
  have h7 : 0 ≤ dist p 0 := by positivity
  nlinarith

/-- Generalized Katz--Tao transfer for the half-parameter cinematic family. -/
lemma halfParameterCinematicFamily_katzTao_general
    (f : SlopeFunction) (h_ns : f.IsNonsingular) (h0 : f 0 = 0)
    (points : DiscreteSet 3) (cinematicScale : ℝ)
    (hscale : 0 < cinematicScale) (hscale_one : cinematicScale ≤ 1)
    (C : ENNReal) (hC : 1 ≤ C) (hC_top : C ≠ ⊤)
    (hKT : points.IsKatzTao cinematicScale 1 C)
    (hunit : points.IsInUnitBall) :
    HasCinematicKatzTaoBound (halfParameterCinematicFamily f points)
      cinematicScale (250 * ENNReal.toReal C) := by
  let c := ENNReal.toReal C
  have hc_nonneg : 0 ≤ c := by positivity
  have hc_ge1 : 1 ≤ c := by
    have h1 : (1 : ENNReal) ≤ C := hC
    have h2 : ENNReal.ofReal c = C := ENNReal.ofReal_toReal hC_top
    have h3 : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal c := by
      simpa using h1.trans (le_of_eq h2.symm)
    exact (ENNReal.ofReal_le_ofReal_iff hc_nonneg).mp h3
  have hc_pos : 0 < c := by linarith
  let C_KT : ℝ := 250 * c
  let phi : Point 3 → C2Function := halfParameterSlopeCurve f
  let family := halfParameterCinematicFamily f points
  have hfamily : family.carrier = phi '' points := by
    simp [family, halfParameterCinematicFamily, phi]
  have hpoints_card : (points.card : ℝ) ≤ c / cinematicScale :=
    unitBall_global_card_general points cinematicScale hscale hscale_one C hC hC_top hKT hunit
  have hfamily_card : family.card ≤ points.card := by
    have himage : phi '' (points : Set (Point 3)) =
        (points.image phi : Set C2Function) := by
      ext g; simp [Set.mem_image]
    have hncard : family.carrier.ncard = (points.image phi).card := by
      rw [hfamily, himage]; exact Set.ncard_coe_finset _
    have hcard : (points.image phi).card ≤ points.card := Finset.card_image_le
    have hcard2 : family.card = family.carrier.ncard := by rfl
    rw [hcard2, hncard]
    exact hcard
  constructor
  · have hreal : (family.card : ℝ) ≤ (points.card : ℝ) := by exact_mod_cast hfamily_card
    calc
      (family.card : ℝ) ≤ (points.card : ℝ) := hreal
      _ ≤ c / cinematicScale := hpoints_card
      _ ≤ C_KT / cinematicScale := by
        dsimp only [C_KT]
        gcongr
        linarith
  · intro center r hr_scale hr_one
    let preimage : Finset (Point 3) :=
      points.filter fun p => phi p ∈ c2Ball center r
    have hpreimage_subset : preimage ⊆ points := Finset.filter_subset _ _
    have himage : family.carrier ∩ c2Ball center r = phi '' preimage := by
      rw [hfamily]
      ext g
      simp only [preimage, Set.mem_inter_iff, Set.mem_image,
        Finset.mem_coe, Finset.mem_filter]
      constructor
      · rintro ⟨⟨p, hp, rfl⟩, hball⟩
        exact ⟨p, ⟨hp, hball⟩, rfl⟩
      · rintro ⟨p, ⟨hp, hball⟩, rfl⟩
        exact ⟨⟨p, hp, rfl⟩, hball⟩
    have hncard : (family.carrier ∩ c2Ball center r).ncard ≤ preimage.card := by
      rw [himage]
      calc
        (phi '' (preimage : Set (Point 3))).ncard ≤
            (preimage : Set (Point 3)).ncard :=
          Set.ncard_image_le (s := (preimage : Set (Point 3))) (f := phi)
        _ = preimage.card := Set.ncard_coe_finset _
    by_cases hempty : preimage = ∅
    · have hzero : (family.carrier ∩ c2Ball center r).ncard = 0 := by
        rw [hempty] at hncard; simp at hncard; omega
      rw [hzero]
      have hCKT_nonneg : 0 ≤ C_KT := by
        dsimp only [C_KT]
        exact mul_nonneg (by norm_num) hc_nonneg
      have hr_nonneg : 0 ≤ r := by linarith
      have h : (0 : ℝ) ≤ C_KT * (r / cinematicScale) :=
        mul_nonneg hCKT_nonneg (div_nonneg hr_nonneg hscale.le)
      simpa [C_KT] using h
    · rcases Finset.nonempty_iff_ne_empty.mpr hempty with ⟨p0, hp0⟩
      have hr : 0 < r := hscale.trans_le hr_scale
      let radius : ℝ := 250 * r
      have hball : ∀ p ∈ preimage, dist p p0 ≤ radius := by
        intro p hp
        have hp_ball : phi p ∈ c2Ball center r := (Finset.mem_filter.mp hp).2
        have hp0_ball : phi p0 ∈ c2Ball center r := (Finset.mem_filter.mp hp0).2
        have hcurve : c2Distance (phi p) (phi p0) ≤ 2 * r := by
          have htriangle := dist_triangle (phi p) center (phi p0)
          have hp_le : dist (phi p) center ≤ r := by
            simpa [c2Distance_eq_dist] using hp_ball
          have hp0_le : dist center (phi p0) ≤ r := by
            simpa [c2Distance_eq_dist, dist_comm] using hp0_ball
          simpa [c2Distance_eq_dist] using htriangle.trans (by linarith)
        have hinverse := halfParameterSlopeCurve_dist_le f h_ns h0 p p0
        dsimp only [phi] at hinverse hcurve
        dsimp only [radius]
        linarith
      have hpreimage_ball : preimage ⊆ points.filter fun p => dist p p0 ≤ radius := by
        intro p hp
        exact Finset.mem_filter.mpr ⟨hpreimage_subset hp, hball p hp⟩
      have hcard : preimage.card ≤ (points.filter fun p => dist p p0 ≤ radius).card :=
        Finset.card_le_card hpreimage_ball
      by_cases hradius_one : radius ≤ 1
      · have hradius_scale : cinematicScale ≤ radius := by
          dsimp only [radius]; nlinarith
        have hKT_ball := hKT p0 radius hradius_scale hradius_one
        have hKT_card : ((points.filter fun p => dist p p0 ≤ radius).card : ENNReal) ≤
            C * Kakeya.realRpowENN (radius / cinematicScale) 1 := by
          simpa [DiscreteSet.ballCount] using hKT_ball
        have hpreimage_real : (preimage.card : ℝ) ≤ C_KT * (r / cinematicScale) := by
          have hcard_enn : (preimage.card : ENNReal) ≤
              ((points.filter fun p => dist p p0 ≤ radius).card : ENNReal) := by
            exact_mod_cast hcard
          have hcard_enn2 : (preimage.card : ENNReal) ≤
              C * Kakeya.realRpowENN (radius / cinematicScale) 1 :=
            hcard_enn.trans hKT_card
          have hrpow : Kakeya.realRpowENN (radius / cinematicScale) 1 =
              ENNReal.ofReal (radius / cinematicScale) := by
            simp [Kakeya.realRpowENN, Real.rpow_one]
          rw [hrpow] at hcard_enn2
          have hmul : C * ENNReal.ofReal (radius / cinematicScale) =
              ENNReal.ofReal (c * (radius / cinematicScale)) := by
            have h2 : C = ENNReal.ofReal c := (ENNReal.ofReal_toReal hC_top).symm
            rw [h2]
            rw [← ENNReal.ofReal_mul hc_nonneg]
          rw [hmul] at hcard_enn2
          have hcard_ofReal : (preimage.card : ENNReal) = ENNReal.ofReal (preimage.card : ℝ) := by simp
          rw [hcard_ofReal] at hcard_enn2
          have hreal : (preimage.card : ℝ) ≤ c * (radius / cinematicScale) :=
            (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hcard_enn2
          calc
            (preimage.card : ℝ) ≤ c * (radius / cinematicScale) := hreal
            _ = C_KT * (r / cinematicScale) := by
              dsimp only [C_KT, radius]
              field_simp [hscale.ne']
        have hncard_real : ((family.carrier ∩ c2Ball center r).ncard : ℝ) ≤
            (preimage.card : ℝ) := by exact_mod_cast hncard
        exact hncard_real.trans hpreimage_real
      · have hradius_large : 1 < radius := by linarith
        have hpreimage_real : (preimage.card : ℝ) ≤ (points.card : ℝ) := by
          exact_mod_cast Finset.card_le_card hpreimage_subset
        have hglobal : (points.card : ℝ) ≤ C_KT * (r / cinematicScale) := by
          calc
            (points.card : ℝ) ≤ c / cinematicScale := hpoints_card
            _ ≤ C_KT * (r / cinematicScale) := by
              have hr_large : 1 / 250 < r := by
                dsimp only [radius] at hradius_large; linarith
              field_simp [hscale.ne']
              nlinarith
        have hncard_real : ((family.carrier ∩ c2Ball center r).ncard : ℝ) ≤
            (preimage.card : ℝ) := by exact_mod_cast hncard
        exact hncard_real.trans (hpreimage_real.trans hglobal)

theorem half_parameter_cinematic_pyz_general :
    HalfParameterCinematicPYZGeneralStatement := by
  intro inputConstant hinput1 hinput_top epsilon hepsilon
  let c := ENNReal.toReal inputConstant
  have hc_nonneg : 0 ≤ c := by positivity
  have hc_ge1 : 1 ≤ c := by
    have h1 : (1 : ENNReal) ≤ inputConstant := hinput1
    have h2 : ENNReal.ofReal c = inputConstant := ENNReal.ofReal_toReal hinput_top
    have h3 : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal c := by
      simpa using h1.trans (le_of_eq h2.symm)
    exact (ENNReal.ofReal_le_ofReal_iff hc_nonneg).mp h3
  have hc_pos : 0 < c := by linarith
  let C_KT : ℝ := 250 * c
  have hC_KT_ge1 : 1 ≤ C_KT := by
    dsimp only [C_KT]
    nlinarith
  let K : ℝ := 37500 / 99
  let D : ℝ := (216 ^ 12 : ℝ)
  let M : ℝ := 40
  let lambda : ℝ := 6000
  have hK1 : 1 ≤ K := by norm_num [K]
  have hD1 : 1 ≤ D := by norm_num [D]
  have hM0 : 0 ≤ M := by norm_num [M]
  have hlambda1 : 1 ≤ lambda := by norm_num [lambda]
  have h_pyz := pyz_input K D C_KT lambda M hK1 hD1 hC_KT_ge1 hlambda1 hM0 epsilon hepsilon
  rcases h_pyz with ⟨delta₀, hdelta₀_pos, hdelta₀_le, h_pyz_main⟩
  refine' ⟨delta₀, hdelta₀_pos, hdelta₀_le, _⟩
  intro f h_ns h0 fineScale hfineScale hfineScale_le points hKT hbox
  have hfineScale_le1 : fineScale ≤ 1 := by
    have h1 : fineScale ≤ delta₀ := hfineScale_le
    have h2 : delta₀ ≤ 1 / lambda := hdelta₀_le
    have h3 : 1 / lambda ≤ 1 := by
      have h4 : 1 ≤ lambda := hlambda1
      exact (div_le_one (by linarith)).mpr h4
    linarith
  have hunit : points.IsInUnitBall := halfBox_implies_unitBall points hbox
  let F_full := halfParameterCinematicFamily f points
  have hKT_full : HasCinematicKatzTaoBound F_full fineScale C_KT :=
    halfParameterCinematicFamily_katzTao_general f h_ns h0 points fineScale
      hfineScale hfineScale_le1 inputConstant hinput1 hinput_top hKT hunit
  let family : Set C2Function := extendedSlopeCurveFamily f
  have h_cinematic : IsCinematicFamily family K D :=
    extended_cinematic_family' f h_ns h0
  have h_jet_bound : ∀ g ∈ family, ∀ x : UnitPoint,
      |g x| ≤ M ∧ |g.firstDeriv x| ≤ M ∧ |g.secondDeriv x| ≤ M := by
    simpa [family, M] using extendedSlopeCurveFamily_jet_bound f h_ns h0
  have h_mem_full : F_full.carrier ⊆ family := by
    intro g hg
    rcases Finset.mem_image.mp hg with ⟨p, hp, rfl⟩
    have h1 := hbox p hp
    exact halfParameterSlopeCurve_mem_extended f p h1
  rcases exists_greedy_separated3 hfineScale F_full.toFinset with
    ⟨S', hS'_sub, hS'_sep, hS'_cover⟩
  let F_sel : FiniteFunctionFamily :=
    ⟨(S' : Set C2Function), Finset.finite_toSet S'⟩
  have h_sel_sub : F_sel.carrier ⊆ F_full.carrier := by
    have h : (S' : Set C2Function) ⊆ (F_full.toFinset : Set C2Function) := by
      exact_mod_cast hS'_sub
    have h2 : F_sel.carrier = (S' : Set C2Function) := by rfl
    have h3 : F_full.carrier = (F_full.toFinset : Set C2Function) := by
      exact (Set.Finite.coe_toFinset F_full.finite).symm
    rw [h2, h3]
    exact h
  have h_sel_family : F_sel.carrier ⊆ family :=
    Set.Subset.trans h_sel_sub h_mem_full
  have h_sel_sep : IsCinematicDeltaSeparated F_sel fineScale := by
    intro g hg h hh hne
    exact hS'_sep g hg h hh hne
  have h_cover : ∀ g ∈ F_full.carrier, ∃ h ∈ F_sel.carrier, c2Distance g h ≤ fineScale := by
    intro g hg
    have h1 : g ∈ F_full.toFinset := by
      have h2 : F_full.carrier = (F_full.toFinset : Set C2Function) :=
        (Set.Finite.coe_toFinset F_full.finite).symm
      rw [h2] at hg
      exact_mod_cast hg
    rcases hS'_cover g h1 with ⟨h, hh_in, h_dist⟩
    have h3 : h ∈ F_sel.carrier := by
      have h4 : F_sel.carrier = (S' : Set C2Function) := by rfl
      rw [h4]
      exact_mod_cast hh_in
    have h_dist' : c2Distance g h < fineScale := by
      rw [c2Distance_eq_dist]
      exact h_dist
    have h5 : c2Distance g h ≤ fineScale := by linarith
    exact ⟨h, h3, h5⟩
  have h_sel_KT : HasCinematicKatzTaoBound F_sel fineScale C_KT :=
    cinematicKatzTao_mono h_sel_sub hKT_full
  have h_bound := h_pyz_main fineScale hfineScale hfineScale_le family h_cinematic h_jet_bound
    F_sel h_sel_family h_sel_sep h_sel_KT
  exact ⟨F_sel, h_sel_sub, h_sel_sep, h_cover, h_bound⟩

end Kakeya.Assouad

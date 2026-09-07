import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.FaithfulActiveCount
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.CroppedConvexOverload

/-!
# Convex overload from the faithful Step-4 witness
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- Faithful fixed-frame convex overload. -/
def LargeSlopeFaithfulConvexOverloadStatement : Prop :=
  ∀ epsilon sigma eta loss : ℝ,
    0 < epsilon → epsilon ≤ 1 / 2 →
    0 < sigma → sigma < 1 →
    0 < eta → eta ≤ epsilon →
    loss ≤ eta →
    1000 * eta ≤ epsilon * sigma ^ 2 →
    ∃ delta0 : ℝ, 0 < delta0 ∧ delta0 ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta0 →
        ∀ cfg : PureWZ2C2GrainConfiguration sigma loss delta,
          ∀ a b : ℝ, b - a ≤ Real.rpow delta epsilon →
            ∀ step4 : LargeSlopeFaithfulStep4Witness
              cfg.family sigma eta a b,
              ∃ W : Set Point3,
                Convex ℝ W ∧
                Kakeya.realRpowENN delta (-eta) * volume W *
                    cfg.family.enncard <
                  (wz1PaperBodyFamily cfg.family).containedCount W

theorem large_slope_faithful_convex_overload :
    LargeSlopeFaithfulConvexOverloadStatement := by
  intro epsilon sigma eta loss hepsilon hepsilonHalf hsigma hsigmaOne
    heta hetaEpsilon hlossEta hgap
  let etaPrime : ℝ := 12 * eta
  have hetaPrime : 0 < etaPrime := by positivity
  rcases paper_tube_segment_ad_direction_bound
      tube_segment_projection_covering_lower_bound
      tube_segment_projection_localization
      ad_covering_comparison_with_constant
      sigma etaPrime hsigma hsigmaOne hetaPrime with
    ⟨deltaDir, hdeltaDirPos, hdeltaDirOne, hdirBound⟩
  let widthExp : ℝ := 36 * eta / sigma
  have hwidthExp : 0 < widthExp := by positivity
  rcases exists_delta_slab_width hwidthExp with
    ⟨deltaWidth, hdeltaWidthPos, hdeltaWidthOne, hwidthBound⟩
  let exponent : ℝ :=
    25 * eta + 36 * eta / sigma - epsilon * sigma
  have hexponent : exponent < 0 := by
    have hnegative := large_slope_exponent_negative hsigma hsigmaOne heta hgap
    dsimp only [exponent]
    linarith
  let K : ℝ := 1024
  have hK : 0 < K := by norm_num [K]
  let absorptionConstant : ℝ :=
    4608 * K * Real.rpow 64 (sigma / 2) / Real.pi
  have hAbsorptionConstant : 0 < absorptionConstant := by
    dsimp only [absorptionConstant]
    have hpow : 0 < Real.rpow 64 (sigma / 2) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hnumerator : 0 < 4608 * K * Real.rpow 64 (sigma / 2) :=
      mul_pos (mul_pos (by norm_num) hK) hpow
    exact div_pos hnumerator Real.pi_pos
  rcases exists_delta_absorb_constant hAbsorptionConstant hexponent with
    ⟨deltaAbsorb, hdeltaAbsorbPos, hdeltaAbsorbOne, habsorb⟩
  let delta0 := min (min deltaDir deltaWidth) deltaAbsorb
  have hdelta0Pos : 0 < delta0 := by positivity
  have hdelta0One : delta0 ≤ 1 :=
    (min_le_left _ _).trans ((min_le_left _ _).trans hdeltaDirOne)
  refine ⟨delta0, hdelta0Pos, hdelta0One, ?_⟩
  intro delta hdelta hdeltaLe cfg a b hba step4
  have hdeltaDir : delta ≤ deltaDir :=
    hdeltaLe.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hdeltaWidth : delta ≤ deltaWidth :=
    hdeltaLe.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hdeltaAbsorb : delta ≤ deltaAbsorb :=
    hdeltaLe.trans (min_le_right _ _)
  have hdeltaOne : delta ≤ 1 := hdeltaLe.trans hdelta0One
  let rho := step4.rho
  have hrho : 0 < rho := step4.rho_pos
  have hrhoQuarter : rho ≤ 1 / 4 := step4.rho_le_quarter
  have hbaPos : 0 < b - a := by
    have hsqrtPos : 0 < Real.sqrt rho := Real.sqrt_pos.mpr hrho
    rw [step4.sqrt_rho_eq] at hsqrtPos
    linarith
  have hrhoUpper : rho ≤ 64 * Real.rpow delta (2 * epsilon) := by
    have hsq : (b - a) ^ 2 ≤ (Real.rpow delta epsilon) ^ 2 := by
      exact (sq_le_sq₀ (by linarith)
        (Real.rpow_nonneg hdelta.le _)).2 hba
    have hrpowSq : (Real.rpow delta epsilon) ^ 2 =
        Real.rpow delta (2 * epsilon) := by
      calc
        (Real.rpow delta epsilon) ^ 2 =
            Real.rpow delta epsilon * Real.rpow delta epsilon := by ring
        _ = Real.rpow delta (epsilon + epsilon) :=
          (Real.rpow_add hdelta _ _).symm
        _ = Real.rpow delta (2 * epsilon) := by congr 1 <;> ring
    change step4.rho ≤ 64 * Real.rpow delta (2 * epsilon)
    rw [step4.rho_eq, ← hrpowSq]
    exact mul_le_mul_of_nonneg_left hsq (by norm_num)
  let tau : ℝ := Real.sqrt rho *
    Real.rpow delta (-(36 * eta / sigma))
  have htau : 0 ≤ tau := mul_nonneg (Real.sqrt_nonneg rho)
    (Real.rpow_nonneg hdelta.le _)
  have htwoDelta : 2 * delta ≤ tau := by
    exact hwidthBound delta rho hdelta hdeltaWidth step4.delta_le_rho
  have hsqrtTau : Real.sqrt rho ≤ tau := by
    dsimp only [tau]
    have hpow : 1 ≤ Real.rpow delta (-(36 * eta / sigma)) :=
      rpow_neg_ge_one hdelta hdeltaOne hwidthExp
    nlinarith [Real.sqrt_nonneg rho]
  let pieceMass : Fin cfg.family.card → Fin step4.prismCount → ENNReal :=
    fun i j => volume (step4.piece i j)
  let total : ENNReal :=
    ENNReal.ofReal
      (36 * Real.rpow delta (12 * eta) * delta ^ 2 * Real.sqrt rho) *
        cfg.family.enncard
  let cap : ENNReal :=
    ENNReal.ofReal (4000 * Real.sqrt rho * delta ^ 2)
  have hprismsNonempty :
      (Finset.univ : Finset (Fin step4.prismCount)).Nonempty :=
    Finset.univ_nonempty_iff.mpr
      (Fin.pos_iff_nonempty.mp step4.prismCount_pos)
  rcases prism_mass_pigeonhole
      (Finset.univ : Finset (Fin cfg.family.card))
      (Finset.univ : Finset (Fin step4.prismCount))
      hprismsNonempty pieceMass total cap
      (by simpa [total, pieceMass] using step4.total_piece_mass)
      (fun i _ j _ => by simpa [cap, pieceMass] using step4.piece_mass_upper i j) with
    ⟨j0, _hj0, hpigeonhole⟩
  let active : Finset (Fin cfg.family.card) :=
    Finset.univ.filter fun i => pieceMass i j0 ≠ 0
  have hpigeonhole' : total ≤
      (step4.prismCount : ENNReal) * cap * (active.card : ENNReal) := by
    simpa [total, cap, active, pieceMass] using hpigeonhole
  have htotalPos : 0 < total := by
    have hfamilyPos : 0 < cfg.family.enncard := by
      have hcard : 0 < cfg.family.card := cfg.extremal.nonempty
      simpa [Kakeya.Streamlined.TubeFamily.enncard] using
        (show (0 : ENNReal) < (cfg.family.card : ENNReal) by exact_mod_cast hcard)
    dsimp only [total]
    have hmassPos : 0 < 36 * Real.rpow delta (12 * eta) *
        delta ^ 2 * Real.sqrt rho := by
      exact mul_pos
        (mul_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos hdelta _))
          (sq_pos_of_pos hdelta))
        (Real.sqrt_pos.mpr hrho)
    exact ENNReal.mul_pos (ENNReal.ofReal_pos.mpr hmassPos |>.ne')
      hfamilyPos.ne'
  have hactivePos : 0 < active.card := by
    by_contra hzero
    have hzero' : (active.card : ENNReal) = 0 := by
      exact_mod_cast Nat.eq_zero_of_not_pos hzero
    rw [hzero', mul_zero] at hpigeonhole'
    exact (not_le_of_gt htotalPos) hpigeonhole'
  have hdir : ∀ i ∈ active,
      |inner ℝ (cfg.family.tube i).direction (step4.prismNormal j0)| ≤
        tau := by
    intro i hi
    have hnonzero : pieceMass i j0 ≠ 0 := (Finset.mem_filter.mp hi).2
    have hlower : ENNReal.ofReal
        (36 * Real.rpow delta etaPrime * delta ^ 2 * Real.sqrt rho) ≤
        volume (step4.piece i j0) := by
      simpa [etaPrime, pieceMass] using step4.piece_mass_lower i j0 hnonzero
    have hbound := hdirBound delta rho (step4.segmentStart i j0)
      hdelta hdeltaDir step4.six_delta_le_rho hrhoQuarter
      (cfg.family.tube i).base (cfg.family.tube i).direction
      (step4.prismNormal j0) (cfg.family.tube i).direction_unit
      (step4.prismNormal_unit j0) (step4.piece i j0)
      (step4.piece_measurable i j0) (step4.piece_sub_segment i j0)
      hlower (step4.piece_local_ad i j0 hnonzero)
    have hreal := direction_bound_to_real hdelta hrho hbound
    have hexp : -(3 * etaPrime / sigma) = -(36 * eta / sigma) := by
      dsimp only [etaPrime]
      ring
    rw [hexp] at hreal
    simpa [tau] using hreal
  let stripWidth : ℝ := Real.sqrt rho + 12 * delta +
    (12 * delta + 2 * Real.sqrt 3) * tau
  let W : Set Point3 := orientedBoxSlab
    (step4.prismCenter j0) (step4.prismNormal j0) stripWidth
  have hconvex : Convex ℝ W := orientedBoxSlab_convex _ _ _
  have hcontain : ∀ i ∈ active,
      wz1PaperTubeCarrier (cfg.family.tube i) ⊆ W := by
    intro i hi
    have hnonzero : volume (step4.piece i j0) ≠ 0 :=
      (Finset.mem_filter.mp hi).2
    have hnonempty : (step4.piece i j0).Nonempty := by
      by_contra hempty
      rw [Set.not_nonempty_iff_eq_empty.mp hempty] at hnonzero
      simp at hnonzero
    rcases hnonempty with ⟨point, hpoint⟩
    have hpaper : point ∈ wz1PaperTubeCarrier (cfg.family.tube i) :=
      step4.fine.subset_body i (step4.piece_sub_fine i j0 hpoint)
    have hslab := step4.prism_transverse j0
      (step4.piece_sub_prism i j0 hpoint)
    intro q hq
    refine ⟨hq.2, ?_⟩
    exact paper_carrier_in_expanded_slab hdelta
      (step4.prismNormal_unit j0) htau (hdir i hi) hpaper hslab q hq
  have hcount : (active.card : ENNReal) ≤
      (wz1PaperBodyFamily cfg.family).containedCount W := by
    let contained := (wz1PaperBodyFamily cfg.family).containedIndices W
    have hsubset : active ⊆ contained := by
      intro i hi
      exact Kakeya.Streamlined.BodyFamily.mem_containedIndices_iff.mpr
        (hcontain i hi)
    have hcard := Finset.card_le_card hsubset
    have hcardENN : (active.card : ENNReal) ≤ (contained.card : ENNReal) := by
      exact_mod_cast hcard
    exact hcardENN
  have hstripWidth : stripWidth ≤ 24 * tau := by
    have hsqrtThree : Real.sqrt 3 ≤ 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
        Real.sqrt_nonneg 3]
    have h12delta : 12 * delta ≤ 6 * tau := by linarith
    have hcoeff : 12 * delta + 2 * Real.sqrt 3 ≤ 16 := by
      have hdeltaLe : delta ≤ 1 := hdeltaOne
      nlinarith
    have hproduct : (12 * delta + 2 * Real.sqrt 3) * tau ≤
        16 * tau := mul_le_mul_of_nonneg_right hcoeff htau
    dsimp only [stripWidth]
    linarith
  have hstripNonneg : 0 ≤ stripWidth := by
    dsimp only [stripWidth]
    positivity
  have hvolume : volume W ≤ ENNReal.ofReal (K * tau) := by
    calc
      volume W ≤ ENNReal.ofReal (24 * stripWidth) :=
        oriented_box_slab_volume _ _ _ (step4.prismNormal_unit j0)
          hstripNonneg
      _ ≤ ENNReal.ofReal (24 * (24 * tau)) := by gcongr
      _ ≤ ENNReal.ofReal (K * tau) := by
        apply ENNReal.ofReal_mono
        dsimp only [K]
        nlinarith
  refine ⟨W, hconvex, ?_⟩

  have hprismReal : (step4.prismCount : ℝ) ≤
      Real.rpow delta (-(12 * eta)) *
        Real.rpow rho ((-1 + sigma) / 2) := by
    exact pureWZ2_faithful_prism_upper_toReal hdelta hrho
      step4.prism_card_upper
  have hpigeonholeReal :
      36 * Real.rpow delta (12 * eta) * delta ^ 2 *
          Real.sqrt rho * (cfg.family.card : ℝ) ≤
        (step4.prismCount : ℝ) *
          (4000 * Real.sqrt rho * delta ^ 2) * (active.card : ℝ) := by
    apply pureWZ2_faithful_pigeonhole_toReal hdelta hrho
    simpa [total, cap, Kakeya.Streamlined.TubeFamily.enncard] using
      hpigeonhole'
  have hactiveReal :
      (9 / 1000 : ℝ) * Real.rpow delta (24 * eta) *
          Real.rpow rho ((1 - sigma) / 2) * (cfg.family.card : ℝ) ≤
        (active.card : ℝ) :=
    pureWZ2_faithful_active_count_from_pigeonhole hdelta hrho
      (by positivity) (by positivity) hpigeonholeReal hprismReal
  have hcountReal : (active.card : ℝ) ≤
      ((wz1PaperBodyFamily cfg.family).containedCount W).toReal := by
    have hfinite : (wz1PaperBodyFamily cfg.family).containedCount W ≠ ⊤ := by
      simp [Kakeya.Streamlined.BodyFamily.containedCount]
    have h := ENNReal.toReal_mono hfinite hcount
    simpa [ENNReal.toReal_natCast] using h
  have hactiveCount :
      (9 / 1000 : ℝ) * Real.rpow delta (24 * eta) *
          Real.rpow rho ((1 - sigma) / 2) * (cfg.family.card : ℝ) ≤
        ((wz1PaperBodyFamily cfg.family).containedCount W).toReal :=
    hactiveReal.trans hcountReal
  have hvolumeFinite : volume W ≠ ⊤ := by
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hvolume
  have hvolumeReal : (volume W).toReal ≤
      K * Real.sqrt rho * Real.rpow delta (-(36 * eta / sigma)) := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hvolume
    rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ K * tau)] at h
    simpa [tau, mul_assoc] using h
  have hfamilyPos : 0 < (cfg.family.card : ℝ) := by
    exact_mod_cast cfg.extremal.nonempty
  have habsorbReal :
      4608 * K * Real.rpow 64 (sigma / 2) / Real.pi <
        Real.rpow delta
          (12 * eta + 13 * eta + 36 * eta / sigma - epsilon * sigma) := by
    have h := habsorb delta hdelta hdeltaAbsorb
    dsimp only [absorptionConstant, exponent] at h
    convert h using 1 <;> ring
  have hfinalReal : Real.rpow delta (-eta) * (volume W).toReal *
      (cfg.family.card : ℝ) <
        ((wz1PaperBodyFamily cfg.family).containedCount W).toReal :=
    pureWZ2_faithful_overload_finish hdelta hsigma heta hepsilon
      hbaPos hfamilyPos K hK step4.rho_eq hvolumeReal hactiveCount hba
      habsorbReal
  have hfamilyFinite : cfg.family.enncard ≠ ⊤ := by
    simp [Kakeya.Streamlined.TubeFamily.enncard]
  have hcountFinite :
      (wz1PaperBodyFamily cfg.family).containedCount W ≠ ⊤ := by
    simp [Kakeya.Streamlined.BodyFamily.containedCount]
  have hlhs : Kakeya.realRpowENN delta (-eta) * volume W *
      cfg.family.enncard =
    ENNReal.ofReal (Real.rpow delta (-eta) * (volume W).toReal *
      (cfg.family.card : ℝ)) := by
    have hpowNonneg : 0 ≤ Real.rpow delta (-eta) :=
      Real.rpow_nonneg hdelta.le _
    have hvolNonneg : 0 ≤ (volume W).toReal := ENNReal.toReal_nonneg
    calc
      Kakeya.realRpowENN delta (-eta) * volume W * cfg.family.enncard =
        ENNReal.ofReal (Real.rpow delta (-eta)) *
          ENNReal.ofReal (volume W).toReal *
            ENNReal.ofReal (cfg.family.card : ℝ) := by
          rw [ENNReal.ofReal_toReal hvolumeFinite]
          simp [Kakeya.realRpowENN, Kakeya.Streamlined.TubeFamily.enncard]
      _ = ENNReal.ofReal
          (Real.rpow delta (-eta) * (volume W).toReal) *
            ENNReal.ofReal (cfg.family.card : ℝ) := by
          rw [ENNReal.ofReal_mul hpowNonneg]
      _ = ENNReal.ofReal (Real.rpow delta (-eta) *
          (volume W).toReal * (cfg.family.card : ℝ)) := by
          rw [ENNReal.ofReal_mul (mul_nonneg hpowNonneg hvolNonneg)]
  have hcountEq :
      (wz1PaperBodyFamily cfg.family).containedCount W =
        ENNReal.ofReal
          ((wz1PaperBodyFamily cfg.family).containedCount W).toReal :=
    (ENNReal.ofReal_toReal hcountFinite).symm
  rw [hlhs, hcountEq]
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg
    (mul_nonneg (mul_nonneg (Real.rpow_nonneg hdelta.le _)
      ENNReal.toReal_nonneg) hfamilyPos.le)).2 hfinalReal

end Kakeya.Assouad

end

import MyLeanRepo.Kakeya.Assouad.AbsorptionHelpers
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.FrostmanToKatzTaoWeightedCard
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterLocalFrostmanBlockPruningStatement
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterLocalFullBlockHelpers

/-!
# Prune a Frostman parameter block

Apply weighted Frostman-to-Katz--Tao extraction at exponent `1-epsilon²`,
absorb its scale-dependent loss using the nineteen-power cardinality margin,
and transport the selected subset back to the original parameter scale.
-/

namespace Kakeya.Assouad

private lemma parameter_local_frostman_block_pruning_inner
    {delta epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C lambda : ENNReal}
    {clustered :
      TubeParameterClusterFrostmanData F Y C lambda delta}
    {blockScale : ℝ}
    (h_block_pos : 0 < blockScale)
    (h_fine_le : delta ≤ blockScale)
    (h_ten_lt : 10 * delta < blockScale)
    (h_small : 100 * blockScale ≤ 1)
    (h_sep :
      Real.rpow delta (1 - epsilon ^ 2) <
        blockScale / 10)
    {blockCenter : Point 3}
    {candidatePoints : DiscreteSet 3}
    (h_cand_nonempty : candidatePoints.Nonempty)
    (h_cand_sub : candidatePoints ⊆ clustered.points)
    (h_cand_contain :
      ∀ p ∈ candidatePoints,
        dist p blockCenter ≤ blockScale / 10)
    {c0 : ℝ}
    (h_c0 :
      ∀ i, clustered.shading.carrier i ≠ ∅ →
        |(tubeParams i).c - c0| ≤ delta / 2)
    (h_eps_pos : 0 < epsilon)
    (h_eps_lt : epsilon < 1 / 10)
    (h_delta_pos : 0 < delta)
    (h_frostman :
      DiscreteSet.IsFrostman
        (candidatePoints.image
          (fun p =>
            blockScale⁻¹ • (p - blockCenter)))
        (delta / blockScale)
        (1 - epsilon ^ 2)
        (Kakeya.realRpowENN
          (delta / blockScale)
          (-12 * epsilon ^ 2)))
    (h_cardinality :
      Kakeya.realRpowENN
          (delta / blockScale)
          (-(1 - epsilon ^ 2)) ≤
        Kakeya.realRpowENN
            (delta / blockScale)
            (-12 * epsilon ^ 2) *
          DiscreteSet.enncard
            (candidatePoints.image
              (fun p =>
                blockScale⁻¹ • (p - blockCenter))))
    (h_absorb :
      weightedFrostmanToKatzTaoConstant
            (1 - epsilon ^ 2) *
          ENNReal.ofReal
            (1 + Real.log (delta / blockScale)⁻¹) *
          Kakeya.realRpowENN
            (delta / blockScale)
            (7 * epsilon ^ 2) ≤
        100000) :
    Nonempty
      (ParameterLocalFrostmanBlockPruningData
        (clustered := clustered)
        (epsilon := epsilon)
        candidatePoints blockCenter blockScale) := by
  set fineScale : ℝ := delta / blockScale with hfineScale_def
  set normalized : DiscreteSet 3 :=
    candidatePoints.image
      (fun p => blockScale⁻¹ • (p - blockCenter))
      with hnormalized_def
  set s : ℝ := 1 - epsilon ^ 2 with hs_def
  set cardS : ℝ := 1 - 20 * epsilon ^ 2 with hcardS_def
  set f : Point 3 → Point 3 :=
    fun p => blockScale⁻¹ • (p - blockCenter)
      with hf_def
  set g : Point 3 → Point 3 :=
    fun q => blockScale • q with hg_def
  have hs_pos : 0 < s := by
    have h1 : epsilon ^ 2 < 1 / 100 := by
      nlinarith
    nlinarith
  have hs_le_one : s ≤ 1 := by
    nlinarith
  have hcardS_pos : 0 < cardS := by
    dsimp only [cardS]
    have h1 : epsilon ^ 2 < 1 / 100 := by
      nlinarith
    nlinarith
  have h_fine_pos : 0 < fineScale := by
    dsimp only [fineScale]
    positivity
  have h_fine_lt_one : fineScale < 1 := by
    dsimp only [fineScale]
    have h : delta < blockScale := by
      linarith
    exact (div_lt_one h_block_pos).mpr h
  have h_norm_nonempty : normalized.Nonempty := by
    rw [hnormalized_def]
    exact h_cand_nonempty.image _
  have h_norm_unit : normalized.IsInUnitBall := by
    rw [hnormalized_def]
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨p, hp, rfl⟩
    have h1 :
        dist p blockCenter ≤ blockScale / 10 :=
      h_cand_contain p hp
    have h2 :
        ‖blockScale⁻¹ • (p - blockCenter)‖ =
          blockScale⁻¹ * ‖p - blockCenter‖ := by
      have h21 :
          ‖blockScale⁻¹ • (p - blockCenter)‖ =
            |blockScale⁻¹| * ‖p - blockCenter‖ :=
        norm_smul _ _
      have h22 : |blockScale⁻¹| = blockScale⁻¹ := by
        rw [abs_of_pos] <;> positivity
      rw [h21, h22]
    have h3 :
        dist
            (blockScale⁻¹ • (p - blockCenter)) 0 =
          blockScale⁻¹ * dist p blockCenter := by
      simpa [dist_eq_norm] using h2
    rw [h3]
    have h4 :
        blockScale⁻¹ * dist p blockCenter ≤ 1 / 10 := by
      calc
        blockScale⁻¹ * dist p blockCenter ≤
            blockScale⁻¹ * (blockScale / 10) := by
          gcongr
        _ = 1 / 10 := by
          field_simp [h_block_pos.ne']
    linarith
  have hC_one :
      1 ≤ Kakeya.realRpowENN fineScale
        (-12 * epsilon ^ 2) := by
    simp only [Kakeya.realRpowENN]
    rw [ENNReal.one_le_ofReal]
    have hzero_exp :
        -12 * epsilon ^ 2 ≤ 0 := by
      nlinarith [sq_nonneg epsilon]
    simpa using
      Real.rpow_le_rpow_of_exponent_ge
        h_fine_pos h_fine_lt_one.le hzero_exp
  have hC_top :
      Kakeya.realRpowENN fineScale
        (-12 * epsilon ^ 2) ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  have h_frostman' :
      normalized.IsFrostman fineScale s
        (Kakeya.realRpowENN fineScale
          (-12 * epsilon ^ 2)) := by
    simpa [fineScale, normalized, s,
      Kakeya.realRpowENN] using h_frostman
  have h_cardinality' :
      Kakeya.realRpowENN fineScale (-s) ≤
        Kakeya.realRpowENN fineScale
            (-12 * epsilon ^ 2) *
          normalized.enncard := by
    simpa [fineScale, normalized, s] using
      h_cardinality
  rcases frostman_to_katz_tao_weighted_card
      3 s hs_pos (hs_le_one.trans (by norm_num)) with
    ⟨_hextraction_one, _hextraction_top, hExtract⟩
  rcases hExtract fineScale
      (Kakeya.realRpowENN fineScale
        (-12 * epsilon ^ 2))
      h_fine_pos h_fine_lt_one hC_one hC_top
      normalized h_norm_nonempty h_norm_unit
      h_frostman' h_cardinality' with
    ⟨A', hA'_nonempty, hA'_sub, hA'_kt, hA'_card⟩
  have hA'_card_target :
      Kakeya.realRpowENN fineScale (-cardS) ≤
        100000 * A'.enncard := by
    have hexponent :
        -cardS = -s + 19 * epsilon ^ 2 := by
      dsimp only [cardS, s]
      ring
    have hconstant_combine :
        Kakeya.realRpowENN fineScale
              (-12 * epsilon ^ 2) *
            Kakeya.realRpowENN fineScale
              (19 * epsilon ^ 2) =
          Kakeya.realRpowENN fineScale
            (7 * epsilon ^ 2) := by
      rw [← realRpowENN_add h_fine_pos]
      congr 1
      ring
    calc
      Kakeya.realRpowENN fineScale (-cardS)
          = Kakeya.realRpowENN fineScale (-s) *
              Kakeya.realRpowENN fineScale
                (19 * epsilon ^ 2) := by
            rw [hexponent, realRpowENN_add h_fine_pos]
      _ ≤
          (weightedFrostmanToKatzTaoConstant s *
              ENNReal.ofReal
                (1 + Real.log fineScale⁻¹) *
              Kakeya.realRpowENN fineScale
                (-12 * epsilon ^ 2) *
              A'.enncard) *
            Kakeya.realRpowENN fineScale
              (19 * epsilon ^ 2) := by
        gcongr
      _ =
          (weightedFrostmanToKatzTaoConstant s *
              ENNReal.ofReal
                (1 + Real.log fineScale⁻¹) *
              Kakeya.realRpowENN fineScale
                (7 * epsilon ^ 2)) *
            A'.enncard := by
        rw [← hconstant_combine]
        ring
      _ ≤ 100000 * A'.enncard := by
        gcongr
  set sourcePoints : DiscreteSet 3 :=
    candidatePoints.filter (fun p => f p ∈ A')
      with hsourcePoints_def
  have h_source_sub :
      sourcePoints ⊆ candidatePoints :=
    Finset.filter_subset _ _
  have h_source_nonempty : sourcePoints.Nonempty := by
    rcases hA'_nonempty with ⟨q, hq⟩
    have hq' : q ∈ normalized := hA'_sub hq
    rw [hnormalized_def] at hq'
    rcases Finset.mem_image.mp hq' with
      ⟨p, hp, hfp⟩
    have hfp' : f p = q := by
      simpa [hf_def] using hfp
    have hp_source : p ∈ sourcePoints := by
      rw [hsourcePoints_def, Finset.mem_filter]
      exact ⟨hp, by simpa [hfp'] using hq⟩
    exact ⟨p, hp_source⟩
  have h_f_inj : Function.Injective f := by
    intro p q h
    have h1 :
        blockScale⁻¹ • (p - blockCenter) =
          blockScale⁻¹ • (q - blockCenter) :=
      h
    apply_fun (fun x => blockScale • x) at h1
    have h2 :
        p - blockCenter = q - blockCenter := by
      simpa [smul_smul, h_block_pos.ne'] using h1
    simpa using h2
  have h_image : sourcePoints.image f = A' := by
    ext q
    simp only [hsourcePoints_def, Finset.mem_image,
      Finset.mem_filter]
    constructor
    · rintro ⟨p, ⟨hp_cand, hp_A'⟩, rfl⟩
      exact hp_A'
    · intro hq
      have hq' : q ∈ normalized := hA'_sub hq
      rw [hnormalized_def] at hq'
      rcases Finset.mem_image.mp hq' with
        ⟨p, hp, hfp⟩
      have hfp' : f p = q := by
        simpa [hf_def] using hfp
      exact
        ⟨p, ⟨hp, by simpa [hfp'] using hq⟩, hfp'⟩
  have h_source_card :
      sourcePoints.enncard = A'.enncard := by
    have h :
        (sourcePoints.image f).card =
          sourcePoints.card :=
      Finset.card_image_of_injective _ h_f_inj
    rw [h_image] at h
    have h' : sourcePoints.card = A'.card := h.symm
    have h'' :
        (sourcePoints.card : ENNReal) =
          (A'.card : ENNReal) := by
      rw [h']
    simpa [DiscreteSet.enncard] using h''
  set centeredPoints : DiscreteSet 3 :=
    sourcePoints.image (fun p => p - blockCenter)
      with hcenteredPoints_def
  have h_scale_eq :
      ∀ p : Point 3, g (f p) = p - blockCenter := by
    intro p
    simp only [hg_def, hf_def]
    rw [smul_smul, mul_inv_cancel₀ h_block_pos.ne',
      one_smul]
  have h_g_inj : Function.Injective g := by
    intro q1 q2 h
    have h' :
        blockScale⁻¹ • g q1 =
          blockScale⁻¹ • g q2 := by
      rw [h]
    simpa [hg_def, smul_smul, h_block_pos.ne']
      using h'
  have h_centered_alt :
      centeredPoints = A'.image g := by
    ext y
    simp only [hcenteredPoints_def, hsourcePoints_def,
      Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨p, ⟨hp_cand, hp_A'⟩, rfl⟩
      exact ⟨f p, hp_A', h_scale_eq p⟩
    · rintro ⟨q, hq, rfl⟩
      have hq' : q ∈ normalized := hA'_sub hq
      rw [hnormalized_def] at hq'
      rcases Finset.mem_image.mp hq' with
        ⟨p, hp, hfp⟩
      have hfp' : f p = q := by
        simpa [hf_def] using hfp
      refine ⟨p, ⟨hp, by simpa [hfp'] using hq⟩, ?_⟩
      have h_eq : p - blockCenter = g q := by
        have h5 : g (f p) = p - blockCenter :=
          h_scale_eq p
        have h6 : g (f p) = g q := by
          rw [hfp']
        rw [h6] at h5
        exact h5.symm
      exact h_eq
  have h_centered_nonempty :
      centeredPoints.Nonempty := by
    rw [h_centered_alt]
    exact hA'_nonempty.image _
  have h_centered_card :
      centeredPoints.enncard = A'.enncard := by
    have h1 : centeredPoints.card = A'.card := by
      rw [h_centered_alt]
      exact Finset.card_image_of_injective _ h_g_inj
    have h2 :
        (centeredPoints.card : ENNReal) =
          (A'.card : ENNReal) := by
      rw [h1]
    simpa [DiscreteSet.enncard] using h2
  have h_ballCount_eq :
      ∀ (z : Point 3) (R : ℝ),
        centeredPoints.ballCount z R =
          A'.ballCount
            (blockScale⁻¹ • z) (R / blockScale) := by
    intro z R
    have h_dist :
        ∀ q : Point 3,
          dist (g q) z =
            blockScale *
              dist q (blockScale⁻¹ • z) := by
      intro q
      have h1 :
          g q - z =
            blockScale •
              (q - blockScale⁻¹ • z) := by
        simp only [hg_def]
        have h2 :
            blockScale • (blockScale⁻¹ • z) = z := by
          rw [smul_smul,
            mul_inv_cancel₀ h_block_pos.ne', one_smul]
        calc
          blockScale • q - z =
              blockScale • q -
                blockScale • (blockScale⁻¹ • z) := by
            rw [h2]
          _ =
              blockScale •
                (q - blockScale⁻¹ • z) := by
            rw [smul_sub]
      calc
        dist (g q) z = ‖g q - z‖ := by
          rw [dist_eq_norm]
        _ =
            ‖blockScale •
              (q - blockScale⁻¹ • z)‖ := by
          rw [h1]
        _ =
            ‖blockScale‖ *
              ‖q - blockScale⁻¹ • z‖ := by
          rw [norm_smul]
        _ =
            |blockScale| *
              ‖q - blockScale⁻¹ • z‖ := by
          rw [Real.norm_eq_abs]
        _ =
            blockScale *
              ‖q - blockScale⁻¹ • z‖ := by
          rw [abs_of_pos h_block_pos]
        _ =
            blockScale *
              dist q (blockScale⁻¹ • z) := by
          rw [← dist_eq_norm]
    have h_iff :
        ∀ q : Point 3,
          dist (g q) z ≤ R ↔
            dist q (blockScale⁻¹ • z) ≤
              R / blockScale := by
      intro q
      rw [h_dist q]
      constructor
      · intro h
        have h_pos : 0 < blockScale := h_block_pos
        have :
            dist q (blockScale⁻¹ • z) =
              (blockScale *
                dist q (blockScale⁻¹ • z)) /
                  blockScale := by
          field_simp [h_pos.ne']
        rw [this]
        gcongr
      · intro h
        have h_pos : 0 < blockScale := h_block_pos
        have :
            blockScale * (R / blockScale) = R := by
          field_simp [h_pos.ne']
        calc
          blockScale *
              dist q (blockScale⁻¹ • z) ≤
            blockScale * (R / blockScale) := by
              gcongr
          _ = R := this
    have h_filter1 :
        centeredPoints.filter
            (fun y => dist y z ≤ R) =
          (A'.filter
            (fun q => dist (g q) z ≤ R)).image g := by
      rw [h_centered_alt]
      exact Finset.filter_image
    have h_filter2 :
        A'.filter (fun q => dist (g q) z ≤ R) =
          A'.filter
            (fun q =>
              dist q (blockScale⁻¹ • z) ≤
                R / blockScale) := by
      apply Finset.filter_congr
      intro q _
      exact h_iff q
    rw [DiscreteSet.ballCount, DiscreteSet.ballCount,
      h_filter1, h_filter2]
    rw [Finset.card_image_of_injective _ h_g_inj]
  have h_kt_centered :
      centeredPoints.IsKatzTao delta s 100 := by
    intro z R hR_delta hR_one
    by_cases hR_block : R ≤ blockScale
    · have h1 : fineScale ≤ R / blockScale := by
        dsimp only [fineScale]
        exact div_le_div_of_nonneg_right
          hR_delta h_block_pos.le
      have h2 : R / blockScale ≤ 1 :=
        (div_le_one h_block_pos).mpr hR_block
      rw [h_ballCount_eq z R]
      have h4 :=
        hA'_kt (blockScale⁻¹ • z)
          (R / blockScale) h1 h2
      have h5 :
          (R / blockScale) / fineScale =
            R / delta := by
        dsimp only [fineScale]
        field_simp [h_delta_pos.ne', h_block_pos.ne']
      rw [h5] at h4
      exact h4
    · have hR_block' : blockScale ≤ R := by
        linarith
      have hA'_unit : A'.IsInUnitBall := by
        intro q hq
        exact h_norm_unit q (hA'_sub hq)
      have h_total :
          A'.ballCount 0 1 = A'.enncard := by
        have h1 :
            A'.filter (fun y => dist y 0 ≤ 1) = A' := by
          ext p
          simp only [Finset.mem_filter]
          constructor
          · rintro ⟨_, _⟩
            tauto
          · intro hp
            exact ⟨hp, hA'_unit p hp⟩
        simp only [DiscreteSet.ballCount, h1]
        rfl
      have h6 :
          A'.enncard ≤
            100 *
              Kakeya.realRpowENN (1 / fineScale) s := by
        have h7 :=
          hA'_kt 0 1 (by linarith [h_fine_pos])
            (by norm_num)
        rw [h_total] at h7
        exact h7
      have h8 :
          centeredPoints.ballCount z R ≤
            centeredPoints.enncard := by
        have h_filter_card :
            (centeredPoints.filter
              (fun y => dist y z ≤ R)).card ≤
              centeredPoints.card :=
          Finset.card_le_card (Finset.filter_subset _ _)
        have h_ball :
            centeredPoints.ballCount z R =
              ((centeredPoints.filter
                (fun y => dist y z ≤ R)).card : ENNReal) := by
          simp [DiscreteSet.ballCount]
        have h_enn :
            centeredPoints.enncard =
              (centeredPoints.card : ENNReal) := by
          simp [DiscreteSet.enncard]
        rw [h_ball, h_enn]
        exact_mod_cast h_filter_card
      have h10 : 1 / fineScale ≤ R / delta := by
        dsimp only [fineScale]
        have h11 :
            blockScale / delta ≤ R / delta :=
          div_le_div_of_nonneg_right
            hR_block' h_delta_pos.le
        have h12 :
            1 / (delta / blockScale) =
              blockScale / delta := by
          field_simp [h_delta_pos.ne', h_block_pos.ne']
        rw [h12]
        exact h11
      have h13 :
          Kakeya.realRpowENN (1 / fineScale) s ≤
            Kakeya.realRpowENN (R / delta) s := by
        simp only [Kakeya.realRpowENN]
        exact ENNReal.ofReal_le_ofReal
          (Real.rpow_le_rpow
            (by positivity) h10 hs_pos.le)
      calc
        centeredPoints.ballCount z R ≤
            centeredPoints.enncard := h8
        _ = A'.enncard := h_centered_card
        _ ≤
            100 *
              Kakeya.realRpowENN (1 / fineScale) s := h6
        _ ≤
            100 *
              Kakeya.realRpowENN (R / delta) s := by
          gcongr
  have h_card_centered :
      Kakeya.realRpowENN (blockScale / delta) cardS ≤
        100000 * centeredPoints.enncard := by
    have h1 : blockScale / delta = 1 / fineScale := by
      dsimp only [fineScale]
      field_simp [h_delta_pos.ne', h_block_pos.ne']
    rw [h1]
    have h2 :
        Kakeya.realRpowENN (1 / fineScale) cardS =
          Kakeya.realRpowENN fineScale (-cardS) := by
      simp only [Kakeya.realRpowENN]
      have h31 :
          Real.rpow fineScale⁻¹ cardS =
            (Real.rpow fineScale cardS)⁻¹ := by
        have h_nonneg1 : 0 ≤ fineScale⁻¹ := by
          positivity
        have h_nonneg2 : 0 ≤ fineScale := by
          linarith
        have h_mul :
            Real.rpow (fineScale⁻¹ * fineScale) cardS =
              Real.rpow fineScale⁻¹ cardS *
                Real.rpow fineScale cardS :=
          Real.mul_rpow h_nonneg1 h_nonneg2
        have h_pos :
            fineScale⁻¹ * fineScale = 1 := by
          field_simp [h_fine_pos.ne']
        have h_eq :
            Real.rpow fineScale⁻¹ cardS *
                Real.rpow fineScale cardS =
              1 := by
          rw [← h_mul, h_pos]
          simp
        have h_pos_rpow :
            0 < Real.rpow fineScale cardS :=
          Real.rpow_pos_of_pos h_fine_pos cardS
        exact
          (mul_eq_one_iff_eq_inv₀
            h_pos_rpow.ne').mp h_eq
      have h32 :
          (Real.rpow fineScale cardS)⁻¹ =
            Real.rpow fineScale (-cardS) :=
        Eq.symm (Real.rpow_neg h_fine_pos.le cardS)
      have h33 : 1 / fineScale = fineScale⁻¹ := by
        field_simp [h_fine_pos.ne']
      rw [h33, h31, h32]
    rw [h2, h_centered_card]
    exact hA'_card_target
  have h_source_containment :
      ∀ p ∈ sourcePoints,
        dist p blockCenter ≤ blockScale / 10 :=
    fun p hp => h_cand_contain p (h_source_sub hp)
  have h_source_sub_clustered :
      sourcePoints ⊆ clustered.points := by
    exact h_source_sub.trans h_cand_sub
  let block :
      ParameterLocalFullBlockData clustered epsilon :=
    { blockScale := blockScale
      blockScale_pos := h_block_pos
      fine_le_block := h_fine_le
      blockScale_small := h_small
      separated_scale := h_sep
      localCenter := blockCenter
      sourcePoints := sourcePoints
      sourcePoints_nonempty := h_source_nonempty
      sourcePoints_subset := h_source_sub_clustered
      source_containment := h_source_containment
      centeredPoints := centeredPoints
      centeredPoints_eq := rfl
      centeredPoints_nonempty := h_centered_nonempty
      centered_containment :=
        centeredParameterSet_containment
          h_source_containment
      windowCenter := c0
      local_window :=
        parameterLocalBlock_window
          clustered sourcePoints c0 h_c0
      local_katzTao := h_kt_centered
      local_cardinality := h_card_centered
      local_mass_lower :=
        parameterLocalBlockShading_mass_lower
          clustered sourcePoints h_source_sub_clustered }
  exact
    ⟨{ block := block
       blockScale_eq := rfl
       localCenter_eq := rfl
       sourcePoints_subset_candidate := h_source_sub }⟩

theorem parameter_local_frostman_block_pruning :
    ParameterLocalFrostmanBlockPruningStatement := by
  intro epsilon h_eps_pos h_eps_lt
  refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
  intro delta h_delta_pos h_delta_le
  intro F Y C lambda clustered
  intro blockScale h_block_pos h_fine_le h_ten_lt
    h_small h_sep
  intro blockCenter candidatePoints h_cand_nonempty
    h_cand_sub h_cand_contain
  intro c0 h_c0
  intro fineScale normalized h_frostman h_cardinality
    h_absorb
  exact
    parameter_local_frostman_block_pruning_inner
      h_block_pos h_fine_le h_ten_lt h_small h_sep
      h_cand_nonempty h_cand_sub h_cand_contain h_c0
      h_eps_pos h_eps_lt h_delta_pos
      h_frostman h_cardinality h_absorb

end Kakeya.Assouad

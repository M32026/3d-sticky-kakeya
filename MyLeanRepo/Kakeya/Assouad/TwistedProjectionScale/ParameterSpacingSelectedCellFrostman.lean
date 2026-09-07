import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.CubicGridBallPointCount
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.FrostmanToKatzTaoWeightedCard
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterSpacingLocalCounts
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ScaledUniformTreeFrostman

/-!
# Frostman control inside the selected spacing cell

The exact branching tree below the selected level gives a Frostman estimate
after normalizing the selected cell to unit scale.
-/

noncomputable section

namespace Kakeya.Assouad

def parameterSpacingSelectedCellGeometricConstant
    (base : ℕ) (epsilon : ℝ) : ENNReal :=
  ENNReal.ofReal
      (((2 * base + 1) ^ 3 : ℕ) : ℝ) *
    Kakeya.realRpowENN
      (90 * (base : ℝ))
      (parameterSpacingSuffixDimension epsilon)

lemma parameterSpacing_selectedCell_scaleFactor_eq
    {delta epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C lambda : ENNReal}
    {clustered :
      TubeParameterClusterFrostmanData
        F Y C lambda delta}
    (profile :
      ParameterSpacingProfileAssemblyData
        (epsilon := epsilon) clustered)
    (selectedCell :
      ParameterSpacingSelectedCellData profile) :
    selectedCell.blockScale *
        (profile.tree.base : ℝ) ^
          profile.selected.selectedLevel.val =
      90 * (profile.tree.base : ℝ) := by
  let base := profile.tree.base
  let selectedLevel :=
    profile.selected.selectedLevel.val
  have hbase_pos : (0 : ℝ) < base := by
    exact_mod_cast
      (show 0 < base from
        lt_of_lt_of_le (by norm_num)
          profile.tree.base_ge_three)
  have hrpow_mul :
      Real.rpow (base : ℝ)
            (-(selectedLevel : ℝ)) *
          (base : ℝ) ^ selectedLevel =
        1 := by
    rw [show
      (base : ℝ) ^ selectedLevel =
        Real.rpow (base : ℝ)
          (selectedLevel : ℝ) by
      exact (Real.rpow_natCast
        (base : ℝ) selectedLevel).symm]
    calc
      Real.rpow (base : ℝ)
            (-(selectedLevel : ℝ)) *
          Real.rpow (base : ℝ)
            (selectedLevel : ℝ) =
        Real.rpow (base : ℝ)
          (-(selectedLevel : ℝ) +
            (selectedLevel : ℝ)) :=
          (Real.rpow_add hbase_pos _ _).symm
      _ = 1 := by simp
  rw [selectedCell.blockScale_eq]
  rw [mul_assoc, hrpow_mul, mul_one]

lemma parameterSpacing_selectedCell_fineScale_le_delta_power
    {delta epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C lambda : ENNReal}
    {clustered :
      TubeParameterClusterFrostmanData
        F Y C lambda delta}
    {profile :
      ParameterSpacingProfileAssemblyData
        (epsilon := epsilon) clustered}
    (selectedCell :
      ParameterSpacingSelectedCellData profile)
    (hdelta : 0 < delta) :
    normalizedParameterBlockFineScale
        delta selectedCell.blockScale ≤
      Real.rpow delta (epsilon ^ 2) := by
  have hdenom :
      0 <
        Real.rpow delta (1 - epsilon ^ 2) :=
    Real.rpow_pos_of_pos hdelta _
  have hdelta_split :
      delta =
        Real.rpow delta (1 - epsilon ^ 2) *
          Real.rpow delta (epsilon ^ 2) := by
    calc
      delta = Real.rpow delta 1 :=
        (Real.rpow_one delta).symm
      _ = Real.rpow delta
          ((1 - epsilon ^ 2) + epsilon ^ 2) := by
        congr 1
        ring
      _ =
          Real.rpow delta (1 - epsilon ^ 2) *
            Real.rpow delta (epsilon ^ 2) :=
        Real.rpow_add hdelta _ _
  dsimp only [normalizedParameterBlockFineScale]
  calc
    delta / selectedCell.blockScale ≤
        delta /
          Real.rpow delta (1 - epsilon ^ 2) := by
      apply div_le_div_of_nonneg_left hdelta.le hdenom
      linarith [selectedCell.separated_scale]
    _ = Real.rpow delta (epsilon ^ 2) := by
      apply (div_eq_iff hdenom.ne').2
      simpa [mul_comm] using hdelta_split

lemma parameterSpacing_selectedCell_normalized_frostman
    {delta epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C lambda : ENNReal}
    {clustered :
      TubeParameterClusterFrostmanData
        F Y C lambda delta}
    (profile :
      ParameterSpacingProfileAssemblyData
        (epsilon := epsilon) clustered)
    (selectedCell :
      ParameterSpacingSelectedCellData profile)
    (hdelta : 0 < delta)
    (hdimension :
      0 ≤ parameterSpacingSuffixDimension epsilon) :
    let fineScale :=
      normalizedParameterBlockFineScale
        delta selectedCell.blockScale
    let normalized :=
      normalizedParameterBlock
        selectedCell.points selectedCell.center
          selectedCell.blockScale
    normalized.IsFrostman
      fineScale
      (parameterSpacingSuffixDimension epsilon)
      (ENNReal.ofReal
          (((2 * profile.tree.base + 1) ^ 3 : ℕ) : ℝ) *
        Kakeya.realRpowENN
          (selectedCell.blockScale *
            (profile.tree.base : ℝ) ^
              profile.selected.selectedLevel.val)
          (parameterSpacingSuffixDimension epsilon)) := by
  let base := profile.tree.base
  let selectedLevel :=
    profile.selected.selectedLevel.val
  let maxLevel :=
    profile.tree.levels - selectedLevel
  let scaleFactor :=
    selectedCell.blockScale *
      (base : ℝ) ^ selectedLevel
  let fineScale :=
    normalizedParameterBlockFineScale
      delta selectedCell.blockScale
  let normalized :=
    normalizedParameterBlock
      selectedCell.points selectedCell.center
        selectedCell.blockScale
  let dimension :=
    parameterSpacingSuffixDimension epsilon
  let geometricConstant : ℝ :=
    (((2 * base + 1) ^ 3 : ℕ) : ℝ)
  let N : ℕ → ℕ := fun m =>
    cellCount base selectedCell.points
      (selectedLevel + m)
  let M : ℕ → ℕ := fun m =>
    if hm : m ≤ maxLevel then
      Classical.choose
        (selectedCell_uniform_cell_card
          profile selectedCell (selectedLevel + m)
          (by omega) (by
            dsimp only [maxLevel, selectedLevel] at hm
            omega))
    else 0
  have hbase : 2 ≤ base := by
    exact profile.tree.base_ge_three.trans' (by omega)
  have hselected_lt :
      selectedLevel < profile.tree.levels := by
    exact profile.selected.selectedLevel.is_lt
  have hmaxLevel : 0 < maxLevel := by
    dsimp only [maxLevel]
    omega
  have hblock : 0 < selectedCell.blockScale :=
    selectedCell.blockScale_pos
  have hscaleFactor_eq :
      scaleFactor = 90 * (base : ℝ) := by
    have hbase_pos : (0 : ℝ) < base := by
      exact_mod_cast
        (show 0 < base from
          lt_of_lt_of_le (by norm_num)
            profile.tree.base_ge_three)
    have hrpow_mul :
        Real.rpow (base : ℝ)
              (-(selectedLevel : ℝ)) *
            (base : ℝ) ^ selectedLevel =
          1 := by
      rw [show
        (base : ℝ) ^ selectedLevel =
          Real.rpow (base : ℝ)
            (selectedLevel : ℝ) by
        exact (Real.rpow_natCast
          (base : ℝ) selectedLevel).symm]
      calc
        Real.rpow (base : ℝ)
              (-(selectedLevel : ℝ)) *
            Real.rpow (base : ℝ)
              (selectedLevel : ℝ) =
          Real.rpow (base : ℝ)
            (-(selectedLevel : ℝ) +
              (selectedLevel : ℝ)) :=
            (Real.rpow_add hbase_pos _ _).symm
        _ = 1 := by simp
    calc
      scaleFactor =
          (90 * (base : ℝ) *
              Real.rpow (base : ℝ)
                (-(selectedLevel : ℝ))) *
            (base : ℝ) ^ selectedLevel := by
        dsimp only [scaleFactor, base, selectedLevel]
        rw [selectedCell.blockScale_eq]
      _ = 90 * (base : ℝ) := by
        rw [mul_assoc, hrpow_mul, mul_one]
  have hscaleFactor : 1 ≤ scaleFactor := by
    rw [hscaleFactor_eq]
    have hbase_three : (3 : ℝ) ≤ base := by
      exact_mod_cast profile.tree.base_ge_three
    nlinarith
  have hfine_pos : 0 < fineScale := by
    dsimp only [fineScale,
      normalizedParameterBlockFineScale]
    positivity
  have hfine_mesh :
      1 /
          (scaleFactor *
            (base : ℝ) ^ maxLevel) ≤
        fineScale := by
    have hbase_pos : (0 : ℝ) < base := by
      exact_mod_cast
        (show 0 < base from
          lt_of_lt_of_le (by norm_num)
            profile.tree.base_ge_three)
    have hpow_split :
        (base : ℝ) ^ selectedLevel *
            (base : ℝ) ^ maxLevel =
          (base : ℝ) ^ profile.tree.levels := by
      rw [← pow_add]
      congr 1
      dsimp only [maxLevel, selectedLevel]
      omega
    have hterminal :
        1 / (base : ℝ) ^ profile.tree.levels <
          delta / 3 := by
      have h :=
        profile.tree.terminal_mesh_upper
      have hpow_pos :
          0 < (base : ℝ) ^ profile.tree.levels := by
        positivity
      rw [show
        ((base ^ profile.tree.levels : ℝ)⁻¹) =
          1 / (base : ℝ) ^ profile.tree.levels by
        norm_num] at h
      linarith
    calc
      1 /
            (scaleFactor *
              (base : ℝ) ^ maxLevel) =
          (1 / (base : ℝ) ^ profile.tree.levels) /
            selectedCell.blockScale := by
        dsimp only [scaleFactor]
        rw [mul_assoc, hpow_split]
        field_simp [hblock.ne']
      _ ≤ delta / selectedCell.blockScale := by
        apply div_le_div_of_nonneg_right
        · linarith
        · exact hblock.le
      _ = fineScale := rfl
  have hgeometric : 1 ≤ geometricConstant := by
    have hone :
        (1 : ℝ) ≤ ((2 * base + 1 : ℕ) : ℝ) := by
      exact_mod_cast
        (show 1 ≤ 2 * base + 1 by omega)
    calc
      (1 : ℝ) = 1 ^ (3 : ℕ) := by norm_num
      _ ≤ ((2 * base + 1 : ℕ) : ℝ) ^ (3 : ℕ) := by
        gcongr
      _ = geometricConstant := by
        simp [geometricConstant]
  have hM_spec :
      ∀ m, m ≤ maxLevel →
        0 < M m ∧
        ∀ cell ∈ cubicGridPartition base
            (selectedLevel + m) selectedCell.points,
          cell.card = M m := by
    intro m hm
    have hdata :=
      Classical.choose_spec
        (selectedCell_uniform_cell_card
          profile selectedCell (selectedLevel + m)
          (by omega) (by
            dsimp only [maxLevel, selectedLevel] at hm
            omega))
    simpa [M, hm] using hdata
  have htotal :
      ∀ m, 0 < m → m ≤ maxLevel →
        N m * M m = normalized.card := by
    intro m _hm_pos hm
    have hsame := (hM_spec m hm).2
    have hsum :=
      cubicGridPartition_sum_card
        (base := base)
        (level := selectedLevel + m)
        (A := selectedCell.points)
    rw [Finset.sum_congr rfl
      (fun cell hcell => hsame cell hcell),
      Finset.sum_const] at hsum
    have hsource :
        N m * M m = selectedCell.points.card := by
      simpa [N, cellCount, mul_comm] using hsum
    have hnormalized :
        normalized.card = selectedCell.points.card := by
      dsimp only [normalized,
        normalizedParameterBlock]
      rw [Finset.card_image_of_injective]
      exact frostmanHomothety_injective
        (inv_pos.mpr hblock)
        selectedCell.center
    rwa [hnormalized]
  have hN_pos :
      ∀ m, 0 < m → m ≤ maxLevel → 0 < N m := by
    intro m _hm_pos _hm
    dsimp only [N, cellCount]
    exact
      (cubicGridPartition_nonempty
        selectedCell.points_nonempty).card_pos
  have hball :
      ∀ m x r,
        0 < m →
        m ≤ maxLevel →
        1 / (scaleFactor * (base : ℝ) ^ m) ≤ r →
        r * scaleFactor * (base : ℝ) ^ m < base →
        (normalized.ballCount x r).toReal ≤
          geometricConstant * (M m : ℝ) := by
    intro m x r _hm_pos hm _hmesh_r hr_mesh
    let originalCenter :=
      frostmanHomothetyInv
        selectedCell.blockScale⁻¹
        selectedCell.center x
    let originalRadius :=
      r / selectedCell.blockScale⁻¹
    have hr_pos : 0 < r := by
      have hmesh_pos :
          0 <
            1 /
              (scaleFactor *
                (base : ℝ) ^ m) := by
        positivity
      linarith
    have horiginal_radius :
        originalRadius =
          r * selectedCell.blockScale := by
      dsimp only [originalRadius]
      field_simp [hblock.ne']
    have habsolute_scale :
        originalRadius *
            (base : ℝ) ^ (selectedLevel + m) <
          base := by
      rw [horiginal_radius, pow_add]
      dsimp only [scaleFactor] at hr_mesh
      nlinarith
    have hsame := (hM_spec m hm).2
    have hpoint_count :=
      cubicGrid_ballCount_le_cells_mul_card
        (A := selectedCell.points)
        (base := base)
        (level := selectedLevel + m)
        (cellCard := M m)
        (x := originalCenter)
        (r := originalRadius)
        hsame
    have hcell_count :=
      cubic_grid_ball_cell_bound
        (A := selectedCell.points)
        (base := base)
        (level := selectedLevel + m)
        (x := originalCenter)
        (r := originalRadius)
        hbase
        (by rw [horiginal_radius]; positivity)
        habsolute_scale
    have hpoint_real :
        (selectedCell.points.ballCount
            originalCenter originalRadius).toReal ≤
          geometricConstant * (M m : ℝ) := by
      calc
        (selectedCell.points.ballCount
              originalCenter originalRadius).toReal ≤
            ((((cubicGridPartition base
                (selectedLevel + m)
                selectedCell.points).filter
              (fun cell =>
                ∃ p ∈ cell,
                  dist p originalCenter ≤
                    originalRadius)).card : ENNReal) *
              (M m : ENNReal)).toReal := by
          exact ENNReal.toReal_mono
            (ENNReal.mul_ne_top (by simp) (by simp))
            hpoint_count
        _ =
            (((cubicGridPartition base
                (selectedLevel + m)
                selectedCell.points).filter
              (fun cell =>
                ∃ p ∈ cell,
                  dist p originalCenter ≤
                    originalRadius)).card : ℝ) *
              (M m : ℝ) := by
          simp
        _ ≤ geometricConstant * (M m : ℝ) := by
          gcongr
          simpa [geometricConstant] using
            (show
              (((cubicGridPartition base
                  (selectedLevel + m)
                  selectedCell.points).filter
                (fun cell =>
                  ∃ p ∈ cell,
                    dist p originalCenter ≤
                      originalRadius)).card : ℝ) ≤
                (((2 * base + 1) ^ 3 : ℕ) : ℝ) by
              exact_mod_cast hcell_count)
    have hball_eq :
        normalized.ballCount x r =
          selectedCell.points.ballCount
            originalCenter originalRadius := by
      change
        DiscreteSet.ballCount
            (selectedCell.points.image
              (frostmanHomothety
                selectedCell.blockScale⁻¹
                selectedCell.center) :
              DiscreteSet 3)
            x r =
          selectedCell.points.ballCount
            (frostmanHomothetyInv
              selectedCell.blockScale⁻¹
              selectedCell.center x)
            (r / selectedCell.blockScale⁻¹)
      exact
        frostman_ballCount_image
          (inv_pos.mpr hblock)
          selectedCell.center selectedCell.points x r
    rwa [hball_eq]
  have hbranch :
      ∀ m, 0 < m → m ≤ maxLevel →
        (base : ℝ) ^ ((m : ℝ) * dimension) ≤ N m := by
    intro m _hm_pos hm
    let fineLevel : Fin (profile.tree.levels + 1) :=
      ⟨selectedLevel + m, by
        dsimp only [maxLevel, selectedLevel] at hm
        omega⟩
    have hgrowth :=
      selectedCell_local_growth
        profile selectedCell fineLevel (by
          dsimp only [fineLevel, selectedLevel]
          omega)
    simpa [fineLevel, N, dimension,
      selectedLevel] using hgrowth
  exact
    scaled_uniform_subtree_frostman
      normalized base hbase scaleFactor hscaleFactor
      maxLevel hmaxLevel dimension hdimension
      fineScale hfine_pos hfine_mesh
      geometricConstant hgeometric
      N M htotal hN_pos hball hbranch

theorem exists_parameterSpacing_selectedCell_target_frostman
    (base : ℕ)
    (hbase : 3 ≤ base)
    (epsilon : ℝ)
    (hepsilon : 0 < epsilon)
    (hepsilon_small : epsilon < 1 / 10) :
    ∃ delta₀ : ℝ,
      0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ,
        0 < delta →
        delta ≤ delta₀ →
        ∀ F : Kakeya.Streamlined.TubeFamily delta,
          ∀ Y : Kakeya.Streamlined.TubeShading F,
            ∀ C lambda : ENNReal,
              ∀ clustered :
                  TubeParameterClusterFrostmanData
                    F Y C lambda delta,
                ∀ profile :
                    ParameterSpacingProfileAssemblyData
                      (epsilon := epsilon) clustered,
                  profile.tree.base = base →
                  ∀ selectedCell :
                      ParameterSpacingSelectedCellData profile,
                    let fineScale :=
                      normalizedParameterBlockFineScale
                        delta selectedCell.blockScale
                    let normalized :=
                      normalizedParameterBlock
                        selectedCell.points selectedCell.center
                          selectedCell.blockScale
                    normalized.IsFrostman
                      fineScale
                      (1 - epsilon ^ 2)
                      (Kakeya.realRpowENN
                        fineScale (-12 * epsilon ^ 2)) := by
  let dimension :=
    parameterSpacingSuffixDimension epsilon
  let targetDimension := 1 - epsilon ^ 2
  let fixedConstant :=
    parameterSpacingSelectedCellGeometricConstant
      base epsilon
  have hdimension : 0 ≤ dimension := by
    dsimp only [dimension,
      parameterSpacingSuffixDimension]
    nlinarith [sq_nonneg epsilon]
  have hdimension_target :
      dimension < targetDimension := by
    dsimp only [dimension, targetDimension,
      parameterSpacingSuffixDimension]
    nlinarith [sq_pos_of_pos hepsilon]
  have hfixed_top : fixedConstant ≠ ⊤ := by
    dsimp only [fixedConstant,
      parameterSpacingSelectedCellGeometricConstant]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (by simp [Kakeya.realRpowENN])
  have hpower_pos : 0 < epsilon ^ 4 := by
    positivity
  rcases exists_delta_realRpowENN_bound
      fixedConstant hfixed_top hpower_pos with
    ⟨delta₀, hdelta₀, hdelta₀_one, hfixed⟩
  refine ⟨delta₀, hdelta₀, hdelta₀_one, ?_⟩
  intro delta hdelta hdelta_le
    F Y C lambda clustered profile hprofile_base
    selectedCell
  let fineScale :=
    normalizedParameterBlockFineScale
      delta selectedCell.blockScale
  let normalized :=
    normalizedParameterBlock
      selectedCell.points selectedCell.center
        selectedCell.blockScale
  have hblock : 0 < selectedCell.blockScale :=
    selectedCell.blockScale_pos
  have hfine_pos : 0 < fineScale := by
    dsimp only [fineScale,
      normalizedParameterBlockFineScale]
    positivity
  have hfine_one : fineScale ≤ 1 := by
    dsimp only [fineScale,
      normalizedParameterBlockFineScale]
    apply (div_le_one hblock).2
    linarith [selectedCell.ten_delta_lt]
  have hraw :
      normalized.IsFrostman fineScale dimension
        fixedConstant := by
    have h :=
      parameterSpacing_selectedCell_normalized_frostman
        profile selectedCell hdelta hdimension
    rw [parameterSpacing_selectedCell_scaleFactor_eq
      profile selectedCell] at h
    simpa [normalized, fineScale, dimension,
      fixedConstant,
      parameterSpacingSelectedCellGeometricConstant,
      hprofile_base] using h
  have hboost :
      normalized.IsFrostman fineScale targetDimension
        (fixedConstant *
          Kakeya.realRpowENN fineScale
            (dimension - targetDimension)) :=
    frostman_dimension_boosting
      hraw hfine_pos hdimension hdimension_target
  have hfine_delta :
      fineScale ≤ Real.rpow delta (epsilon ^ 2) := by
    exact parameterSpacing_selectedCell_fineScale_le_delta_power
      selectedCell hdelta
  have hdelta_power :
      Kakeya.realRpowENN delta (-(epsilon ^ 4)) ≤
        Kakeya.realRpowENN fineScale
          (-(epsilon ^ 2)) := by
    simp only [Kakeya.realRpowENN]
    apply ENNReal.ofReal_mono
    calc
      Real.rpow delta (-(epsilon ^ 4)) =
          Real.rpow
            (Real.rpow delta (epsilon ^ 2))
            (-(epsilon ^ 2)) := by
        calc
          Real.rpow delta (-(epsilon ^ 4)) =
              Real.rpow delta
                ((epsilon ^ 2) *
                  (-(epsilon ^ 2))) := by
            congr 1
            ring
          _ =
              Real.rpow
                (Real.rpow delta (epsilon ^ 2))
                (-(epsilon ^ 2)) :=
            Real.rpow_mul hdelta.le
              (epsilon ^ 2) (-(epsilon ^ 2))
      _ ≤ Real.rpow fineScale
          (-(epsilon ^ 2)) := by
        exact Real.rpow_le_rpow_of_nonpos
          hfine_pos hfine_delta
          (by nlinarith [sq_nonneg epsilon])
  have hfixed_fine :
      fixedConstant ≤
        Kakeya.realRpowENN fineScale
          (-(epsilon ^ 2)) :=
    (hfixed delta hdelta hdelta_le).trans
      hdelta_power
  have hconstant :
      fixedConstant *
          Kakeya.realRpowENN fineScale
            (dimension - targetDimension) ≤
        Kakeya.realRpowENN fineScale
          (-12 * epsilon ^ 2) := by
    have hexponent :
        dimension - targetDimension =
          -11 * epsilon ^ 2 := by
      dsimp only [dimension, targetDimension,
        parameterSpacingSuffixDimension]
      ring
    rw [hexponent]
    calc
      fixedConstant *
            Kakeya.realRpowENN fineScale
              (-11 * epsilon ^ 2) ≤
          Kakeya.realRpowENN fineScale
              (-(epsilon ^ 2)) *
            Kakeya.realRpowENN fineScale
              (-11 * epsilon ^ 2) := by
        gcongr
      _ =
          Kakeya.realRpowENN fineScale
            (-12 * epsilon ^ 2) := by
        rw [← realRpowENN_add hfine_pos]
        congr 1
        ring
  change normalized.IsFrostman fineScale targetDimension
    (Kakeya.realRpowENN fineScale
      (-12 * epsilon ^ 2))
  intro x r hfine_r hr_one
  exact (hboost x r hfine_r hr_one).trans (by
    gcongr)

end Kakeya.Assouad

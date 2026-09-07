import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterSpacingProfileAssembly

/-!
# Terminal depth needed by the fixed spacing start level
-/

noncomputable section

namespace Kakeya.Assouad

theorem exists_parameterSpacing_start_depth
    (base : ℕ)
    (hbase : 3 ≤ base)
    (epsilon : ℝ)
    (hepsilon : 0 < epsilon)
    (hepsilon_small : epsilon < 1 / 10) :
    ∃ delta₀ : ℝ,
      0 < delta₀ ∧
      delta₀ ≤ 1 ∧
      ∀ delta : ℝ,
        0 < delta →
        delta ≤ delta₀ →
        ∀ F : Kakeya.Streamlined.TubeFamily delta,
          ∀ Y : Kakeya.Streamlined.TubeShading F,
            ∀ C lambda : ENNReal,
              ∀ clustered :
                  TubeParameterClusterFrostmanData
                    F Y C lambda delta,
                ∀ tree :
                    ParameterSpacingUniformTreeData
                      clustered epsilon,
                  tree.base = base →
                  parameterSpacingStartIndex <
                      tree.levels ∧
                    (parameterSpacingStartIndex : ℝ) /
                        (tree.levels : ℝ) ≤
                      epsilon ^ 2 / 100 := by
  let depthBound : ℕ :=
    Nat.ceil
      (100 * (parameterSpacingStartIndex : ℝ) /
        epsilon ^ 2)
  have heps_sq : 0 < epsilon ^ 2 :=
    sq_pos_of_pos hepsilon
  have hdepth_nonneg :
      0 ≤
        100 * (parameterSpacingStartIndex : ℝ) /
          epsilon ^ 2 := by positivity
  have hdepth_real :
      100 * (parameterSpacingStartIndex : ℝ) /
          epsilon ^ 2 ≤
        (depthBound : ℝ) :=
    Nat.le_ceil _
  have hdepth_start :
      parameterSpacingStartIndex < depthBound + 1 := by
    have heps_sq_small : epsilon ^ 2 < 1 / 100 := by
      nlinarith
    have hratio :
        (parameterSpacingStartIndex : ℝ) <
          100 * (parameterSpacingStartIndex : ℝ) /
            epsilon ^ 2 := by
      have hstart_pos :
          0 < (parameterSpacingStartIndex : ℝ) := by
        norm_num [parameterSpacingStartIndex]
      have hhundred : epsilon ^ 2 < 100 := by
        linarith
      apply (lt_div_iff₀ heps_sq).2
      nlinarith
    have hstart_depth :
        (parameterSpacingStartIndex : ℝ) <
          (depthBound : ℝ) :=
      hratio.trans_le hdepth_real
    exact_mod_cast hstart_depth.trans_le
      (show (depthBound : ℝ) ≤ depthBound + 1 by
        norm_num)
  have hbase_pos : (0 : ℝ) < base := by
    exact_mod_cast
      (show 0 < base from
        lt_of_lt_of_le (by norm_num) hbase)
  let deltaThreshold : ℝ :=
    3 * (base ^ depthBound : ℝ)⁻¹
  have hdeltaThreshold : 0 < deltaThreshold := by
    dsimp only [deltaThreshold]
    positivity
  let delta₀ : ℝ :=
    min (deltaThreshold / 2) (1 / 1000)
  have hdelta₀ : 0 < delta₀ := by
    dsimp only [delta₀]
    positivity
  have hdelta₀_one : delta₀ ≤ 1 :=
    (min_le_right _ _).trans (by norm_num)
  refine ⟨delta₀, hdelta₀, hdelta₀_one, ?_⟩
  intro delta hdelta hdelta_le
    F Y C lambda clustered tree htree_base
  subst base
  have hdelta_threshold :
      delta < deltaThreshold := by
    calc
      delta ≤ delta₀ := hdelta_le
      _ ≤ deltaThreshold / 2 :=
        min_le_left _ _
      _ < deltaThreshold := by
        linarith
  have hlevels_gt :
      depthBound < tree.levels := by
    by_contra hnot
    have hlevels_le :
        tree.levels ≤ depthBound := by omega
    have hpow :
        (tree.base ^ tree.levels : ℝ) ≤
          (tree.base ^ depthBound : ℝ) := by
      exact_mod_cast
        pow_le_pow_right₀
          (show 1 ≤ tree.base by omega)
          hlevels_le
    have hinv :
        (tree.base ^ depthBound : ℝ)⁻¹ ≤
          (tree.base ^ tree.levels : ℝ)⁻¹ :=
      (inv_le_inv₀ (by positivity) (by positivity)).2 hpow
    have hmesh :
        3 * (tree.base ^ depthBound : ℝ)⁻¹ <
          delta :=
      (mul_le_mul_of_nonneg_left
        hinv (by norm_num)).trans_lt
          tree.terminal_mesh_upper
    exact (not_lt_of_ge hdelta_threshold.le) hmesh
  have hstart_available :
      parameterSpacingStartIndex < tree.levels :=
    hdepth_start.trans_le (by omega)
  have hlevels_real :
      (0 : ℝ) < tree.levels := by
    exact_mod_cast tree.levels_pos
  have hdepth_le_levels :
      (depthBound : ℝ) ≤
        (tree.levels : ℝ) := by
    exact_mod_cast hlevels_gt.le
  have hstart_bound :
      (parameterSpacingStartIndex : ℝ) ≤
        (epsilon ^ 2 / 100) *
          (depthBound : ℝ) := by
    have hmul :=
      mul_le_mul_of_nonneg_left
        hdepth_real
        (show 0 ≤ epsilon ^ 2 / 100 by positivity)
    field_simp [heps_sq.ne'] at hmul ⊢
    linarith
  have hnormalized :
      (parameterSpacingStartIndex : ℝ) /
          (tree.levels : ℝ) ≤
        epsilon ^ 2 / 100 := by
    apply (div_le_iff₀ hlevels_real).2
    calc
      (parameterSpacingStartIndex : ℝ)
          ≤ (epsilon ^ 2 / 100) *
              (depthBound : ℝ) := hstart_bound
      _ ≤ (epsilon ^ 2 / 100) *
              (tree.levels : ℝ) := by
        gcongr
  exact ⟨hstart_available, hnormalized⟩

end Kakeya.Assouad

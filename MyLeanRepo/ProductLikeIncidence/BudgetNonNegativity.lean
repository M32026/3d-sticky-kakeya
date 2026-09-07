module

/-
# Budget Non-Negativity Lemmas

Standalone non-negativity proofs for V4 budget exponents, extracted to avoid
whnf timeouts in the large glue file.

## Main results

- `qDiffV4_nonneg`: `0 ≤ qDiffV4 ...`
- `qSizeLossV4_nonneg`: `0 ≤ qSizeLossV4 ...`
-/

public import MyLeanRepo.ProductLikeIncidence.WireBudgetsV4
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

namespace ProductLikeIncidence.ProductReduction

/-- `qDiffV4` is non-negative given basic positivity hypotheses. -/
lemma qDiffV4_nonneg
    {L_exp η_work ε κ0 p_projective τ rho_sel rho_sep : ℝ}
    (hL_exp_pos : 0 < L_exp)
    (hη_work_pos : 0 < η_work)
    (hε_pos : 0 < ε)
    (hκ0_pos : 0 < κ0)
    (hp_nonneg : 0 ≤ p_projective)
    (hτ_pos : 0 < τ)
    (hrho_sel_nonneg : 0 ≤ rho_sel)
    (hrho_sep_nonneg : 0 ≤ rho_sep) :
    0 ≤ qDiffV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep := by
  dsimp only [qDiffV4]
  have h1 : 0 ≤ qKV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep := by
    dsimp only [qKV4, qDensityV4, qK, qProjective, qAbsorb]
    positivity
  have h2 : 0 ≤ qKAV4 L_exp η_work rho_sel rho_sep := by
    dsimp only [qKAV4, alphaProjectionV4, qMassV4, qAbsorb]
    positivity
  have h3 : 0 ≤ qAbsorb η_work := by
    dsimp only [qAbsorb]; positivity
  have h4 : 0 ≤ qNormChunkV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep := by
    dsimp only [qNormChunkV4, qGraphV4, qBox, qAbsorb]
    positivity
  positivity

/-- `qSizeLossV4` is non-negative given basic positivity hypotheses. -/
lemma qSizeLossV4_nonneg
    {L_exp η_work ε κ0 p_projective τ rho_sel rho_sep : ℝ}
    (hL_exp_pos : 0 < L_exp)
    (hη_work_pos : 0 < η_work)
    (hε_pos : 0 < ε)
    (hκ0_pos : 0 < κ0)
    (hp_nonneg : 0 ≤ p_projective)
    (hτ_pos : 0 < τ)
    (hrho_sel_nonneg : 0 ≤ rho_sel)
    (hrho_sep_nonneg : 0 ≤ rho_sep) :
    0 ≤ qSizeLossV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep := by
  dsimp only [qSizeLossV4, qEffV4, qInputV4, qFixedCoordinate, qBox, qAbsorb,
    qKV4, qDensityV4, qK, qProjective, qGraphV4, qNormChunkV4]
  have h1 : 0 ≤ 4 * η_work / τ := by positivity
  positivity

/-- `q_graph_total` (sum of V4 graph budget components) is non-negative. -/
lemma q_graph_total_nonneg
    {L_exp η_work ε κ0 p_projective τ rho_sel rho_sep : ℝ}
    (hL_exp_pos : 0 < L_exp)
    (hη_work_pos : 0 < η_work)
    (hε_pos : 0 < ε)
    (hκ0_pos : 0 < κ0)
    (hp_nonneg : 0 ≤ p_projective)
    (hτ_pos : 0 < τ)
    (hrho_sel_nonneg : 0 ≤ rho_sel)
    (hrho_sep_nonneg : 0 ≤ rho_sep) :
    0 ≤ qInitV3 η_work rho_sel + 2 * rho_sep +
        qGraphV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep +
        qAbsorb η_work + qNormEnergyV3 η_work ε τ κ0 rho_sel rho_sep := by
  have h1 : 0 ≤ qInitV3 η_work rho_sel := by
    dsimp only [qInitV3]; positivity
  have h2 : 0 ≤ (2 * rho_sep : ℝ) := by positivity
  have h3 : 0 ≤ qGraphV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep := by
    dsimp only [qGraphV4, qKV4, qDensityV4, qK, qProjective, qAbsorb]
    <;> positivity
  have h4 : 0 ≤ qAbsorb η_work := by
    dsimp only [qAbsorb]; positivity
  have h5 : 0 ≤ qNormEnergyV3 η_work ε τ κ0 rho_sel rho_sep := by
    dsimp only [qNormEnergyV3, qCoordEnergyV3, rhoExc, qKaufBase, qEnergy,
      qPlan, qKaufman, qBox, qAbsorb]
    <;> positivity
  linarith

/-- `qTotalV4` is non-negative given basic positivity hypotheses. -/
lemma qTotalV4_nonneg
    {L_exp η_work ε κ0 p_projective τ rho_sel rho_sep : ℝ}
    (hL_exp_pos : 0 < L_exp)
    (hη_work_pos : 0 < η_work)
    (hε_pos : 0 < ε)
    (hκ0_pos : 0 < κ0)
    (hp_nonneg : 0 ≤ p_projective)
    (hτ_pos : 0 < τ)
    (hrho_sel_nonneg : 0 ≤ rho_sel)
    (hrho_sep_nonneg : 0 ≤ rho_sep) :
    0 ≤ qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep := by
  have h1 : 0 ≤ qInitV3 η_work rho_sel := by dsimp only [qInitV3] <;> positivity
  have h2 : 0 ≤ (2 * rho_sep : ℝ) := by positivity
  have h3 : 0 ≤ qGraphV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep := by
    dsimp only [qGraphV4, qKV4, qDensityV4, qK, qProjective, qAbsorb] <;> positivity
  have h4 : 0 ≤ qAbsorb η_work := by dsimp only [qAbsorb] <;> positivity
  have h5 : 0 ≤ qDiffV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep :=
    qDiffV4_nonneg hL_exp_pos hη_work_pos hε_pos hκ0_pos hp_nonneg hτ_pos hrho_sel_nonneg hrho_sep_nonneg
  have h6 : 0 ≤ qSizeLossV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep :=
    qSizeLossV4_nonneg hL_exp_pos hη_work_pos hε_pos hκ0_pos hp_nonneg hτ_pos hrho_sel_nonneg hrho_sep_nonneg
  have h7 : 0 ≤ η_work := by linarith
  have h8 : 0 ≤ ζDir p_projective ε κ0 := by dsimp only [ζDir, qProjective] <;> positivity
  have h9 : 0 ≤ ηProj L_exp η_work ε κ0 p_projective := by dsimp only [ηProj, qProjective] <;> positivity
  have h10 : 0 ≤ qNormEnergyV3 η_work ε τ κ0 rho_sel rho_sep := by
    dsimp only [qNormEnergyV3, qCoordEnergyV3, rhoExc, qKaufBase, qEnergy,
      qPlan, qKaufman, qBox, qAbsorb] <;> positivity
  dsimp only [qTotalV4]
  exact add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg h1 h2) h3) h4) (by positivity)) h6) h7) h8) h9) h10

/-- `qNormChunkV4` is non-negative given basic positivity hypotheses. -/
lemma qNormChunkV4_nonneg
    {L_exp η_work ε κ0 p_projective τ rho_sel rho_sep : ℝ}
    (hL_exp_pos : 0 < L_exp)
    (hη_work_pos : 0 < η_work)
    (hε_pos : 0 < ε)
    (hκ0_pos : 0 < κ0)
    (hp_nonneg : 0 ≤ p_projective)
    (hτ_pos : 0 < τ)
    (hrho_sel_nonneg : 0 ≤ rho_sel)
    (hrho_sep_nonneg : 0 ≤ rho_sep) :
    0 ≤ qNormChunkV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep := by
  have h1 : 0 ≤ qGraphV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep := by
    dsimp only [qGraphV4, qKV4, qDensityV4, qK, qProjective, qAbsorb] <;> positivity
  have h2 : 0 ≤ qBox η_work τ := by dsimp only [qBox, qAbsorb]; positivity
  have h3 : 0 ≤ qAbsorb η_work := by dsimp only [qAbsorb]; positivity
  have h4 : qNormChunkV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep =
      qGraphV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep + qBox η_work τ + qAbsorb η_work := by
    dsimp only [qNormChunkV4] <;> rfl
  rw [h4]
  linarith

/-- `qSizeLossV4` is strictly positive given basic positivity hypotheses. -/
lemma qSizeLossV4_pos
    {L_exp η_work ε κ0 p_projective τ rho_sel rho_sep : ℝ}
    (hL_exp_pos : 0 < L_exp)
    (hη_work_pos : 0 < η_work)
    (hε_pos : 0 < ε)
    (hκ0_pos : 0 < κ0)
    (hp_nonneg : 0 ≤ p_projective)
    (hτ_pos : 0 < τ)
    (hrho_sel_nonneg : 0 ≤ rho_sel)
    (hrho_sep_nonneg : 0 ≤ rho_sep) :
    0 < qSizeLossV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep := by
  dsimp only [qSizeLossV4, qEffV4, qInputV4, qFixedCoordinate, qBox, qAbsorb,
    qKV4, qDensityV4, qK, qProjective, qGraphV4, qNormChunkV4]
  have h1 : 0 < 4 * η_work / τ := by positivity
  positivity

end ProductLikeIncidence.ProductReduction
